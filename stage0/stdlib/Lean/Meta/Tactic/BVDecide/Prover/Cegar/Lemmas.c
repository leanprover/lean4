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
lean_object* v_toCold_282_; lean_object* v_currRecDepth_283_; lean_object* v_ref_284_; uint16_t v_optionFlags_285_; uint8_t v_suppressElabErrors_286_; uint8_t v_checkDeprecated_287_; uint8_t v_isRecordingDeps_288_; lean_object* v_ref_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_traceState_292_; lean_object* v_traces_293_; lean_object* v___x_294_; size_t v_sz_295_; size_t v___x_296_; lean_object* v___x_297_; lean_object* v_msg_298_; lean_object* v___x_299_; lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_338_; 
v_toCold_282_ = lean_ctor_get(v___y_279_, 0);
v_currRecDepth_283_ = lean_ctor_get(v___y_279_, 1);
v_ref_284_ = lean_ctor_get(v___y_279_, 2);
v_optionFlags_285_ = lean_ctor_get_uint16(v___y_279_, sizeof(void*)*3);
v_suppressElabErrors_286_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 2);
v_checkDeprecated_287_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 3);
v_isRecordingDeps_288_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 4);
v_ref_289_ = l_Lean_replaceRef(v_ref_275_, v_ref_284_);
lean_inc(v_currRecDepth_283_);
lean_inc_ref(v_toCold_282_);
v___x_290_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_290_, 0, v_toCold_282_);
lean_ctor_set(v___x_290_, 1, v_currRecDepth_283_);
lean_ctor_set(v___x_290_, 2, v_ref_289_);
lean_ctor_set_uint16(v___x_290_, sizeof(void*)*3, v_optionFlags_285_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*3 + 2, v_suppressElabErrors_286_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*3 + 3, v_checkDeprecated_287_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*3 + 4, v_isRecordingDeps_288_);
v___x_291_ = lean_st_ref_get(v___y_280_);
v_traceState_292_ = lean_ctor_get(v___x_291_, 4);
lean_inc_ref(v_traceState_292_);
lean_dec(v___x_291_);
v_traces_293_ = lean_ctor_get(v_traceState_292_, 0);
lean_inc_ref(v_traces_293_);
lean_dec_ref(v_traceState_292_);
v___x_294_ = l_Lean_PersistentArray_toArray___redArg(v_traces_293_);
lean_dec_ref(v_traces_293_);
v_sz_295_ = lean_array_size(v___x_294_);
v___x_296_ = ((size_t)0ULL);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_295_, v___x_296_, v___x_294_);
v_msg_298_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_298_, 0, v_data_274_);
lean_ctor_set(v_msg_298_, 1, v_msg_276_);
lean_ctor_set(v_msg_298_, 2, v___x_297_);
v___x_299_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_298_, v___y_277_, v___y_278_, v___x_290_, v___y_280_);
lean_dec_ref_known(v___x_290_, 3);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_338_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_338_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_338_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v_traceState_305_; lean_object* v_env_306_; lean_object* v_nextMacroScope_307_; lean_object* v_ngen_308_; lean_object* v_auxDeclNGen_309_; lean_object* v_cache_310_; lean_object* v_recordedDeps_311_; lean_object* v_messages_312_; lean_object* v_infoState_313_; lean_object* v_snapshotTasks_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_337_; 
v___x_304_ = lean_st_ref_take(v___y_280_);
v_traceState_305_ = lean_ctor_get(v___x_304_, 4);
v_env_306_ = lean_ctor_get(v___x_304_, 0);
v_nextMacroScope_307_ = lean_ctor_get(v___x_304_, 1);
v_ngen_308_ = lean_ctor_get(v___x_304_, 2);
v_auxDeclNGen_309_ = lean_ctor_get(v___x_304_, 3);
v_cache_310_ = lean_ctor_get(v___x_304_, 5);
v_recordedDeps_311_ = lean_ctor_get(v___x_304_, 6);
v_messages_312_ = lean_ctor_get(v___x_304_, 7);
v_infoState_313_ = lean_ctor_get(v___x_304_, 8);
v_snapshotTasks_314_ = lean_ctor_get(v___x_304_, 9);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_337_ == 0)
{
v___x_316_ = v___x_304_;
v_isShared_317_ = v_isSharedCheck_337_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snapshotTasks_314_);
lean_inc(v_infoState_313_);
lean_inc(v_messages_312_);
lean_inc(v_recordedDeps_311_);
lean_inc(v_cache_310_);
lean_inc(v_traceState_305_);
lean_inc(v_auxDeclNGen_309_);
lean_inc(v_ngen_308_);
lean_inc(v_nextMacroScope_307_);
lean_inc(v_env_306_);
lean_dec(v___x_304_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_337_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint64_t v_tid_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_335_; 
v_tid_318_ = lean_ctor_get_uint64(v_traceState_305_, sizeof(void*)*1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_traceState_305_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_traceState_305_, 0);
lean_dec(v_unused_336_);
v___x_320_ = v_traceState_305_;
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
else
{
lean_dec(v_traceState_305_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_275_);
lean_ctor_set(v___x_323_, 1, v_a_300_);
v___x_324_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_273_, v___x_323_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_324_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_324_);
lean_ctor_set_uint64(v_reuseFailAlloc_334_, sizeof(void*)*1, v_tid_318_);
v___x_326_ = v_reuseFailAlloc_334_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 4, v___x_326_);
v___x_328_ = v___x_316_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_env_306_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_nextMacroScope_307_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_ngen_308_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_auxDeclNGen_309_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v_cache_310_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_recordedDeps_311_);
lean_ctor_set(v_reuseFailAlloc_333_, 7, v_messages_312_);
lean_ctor_set(v_reuseFailAlloc_333_, 8, v_infoState_313_);
lean_ctor_set(v_reuseFailAlloc_333_, 9, v_snapshotTasks_314_);
v___x_328_ = v_reuseFailAlloc_333_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = lean_st_ref_put(v___y_280_, v___x_328_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_322_);
v___x_331_ = v___x_302_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_322_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_339_, lean_object* v_data_340_, lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_339_, v_data_340_, v_ref_341_, v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0(void){
_start:
{
lean_object* v___x_349_; double v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_float_of_nat(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3(void){
_start:
{
lean_object* v___x_354_; double v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1000u);
v___x_355_ = lean_float_of_nat(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object* v_cls_356_, uint8_t v_collapsed_357_, lean_object* v_tag_358_, lean_object* v_opts_359_, uint8_t v_clsEnabled_360_, lean_object* v_oldTraces_361_, lean_object* v_msg_362_, lean_object* v_resStartStop_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v_data_384_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___y_400_; lean_object* v_a_401_; uint8_t v___y_416_; double v___y_448_; 
v_fst_379_ = lean_ctor_get(v_resStartStop_363_, 0);
lean_inc(v_fst_379_);
v_snd_380_ = lean_ctor_get(v_resStartStop_363_, 1);
lean_inc(v_snd_380_);
lean_dec_ref(v_resStartStop_363_);
v_fst_395_ = lean_ctor_get(v_snd_380_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v_snd_380_, 1);
lean_inc(v_snd_396_);
lean_dec(v_snd_380_);
v___x_397_ = l_Lean_trace_profiler;
v___x_398_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_359_, v___x_397_);
if (v___x_398_ == 0)
{
v___y_416_ = v___x_398_;
goto v___jp_415_;
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = l_Lean_trace_profiler_useHeartbeats;
v___x_454_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_359_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; double v___x_458_; double v___x_459_; 
v___x_455_ = l_Lean_trace_profiler_threshold;
v___x_456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_359_, v___x_455_);
v___x_457_ = lean_float_of_nat(v___x_456_);
v___x_458_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3);
v___x_459_ = lean_float_div(v___x_457_, v___x_458_);
v___y_448_ = v___x_459_;
goto v___jp_447_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; double v___x_462_; 
v___x_460_ = l_Lean_trace_profiler_threshold;
v___x_461_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_359_, v___x_460_);
v___x_462_ = lean_float_of_nat(v___x_461_);
v___y_448_ = v___x_462_;
goto v___jp_447_;
}
}
v___jp_381_:
{
lean_object* v___x_385_; 
lean_inc(v___y_382_);
v___x_385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_361_, v_data_384_, v___y_382_, v___y_383_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec_ref_known(v___x_385_, 1);
v___x_386_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_379_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_fst_379_);
v_a_387_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_385_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_385_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
v___jp_399_:
{
uint8_t v_result_402_; lean_object* v___x_403_; lean_object* v___x_404_; double v___x_405_; lean_object* v_data_406_; 
v_result_402_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_fst_379_);
v___x_403_ = lean_box(v_result_402_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0);
lean_inc_ref(v_tag_358_);
lean_inc_ref(v___x_404_);
lean_inc(v_cls_356_);
v_data_406_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_406_, 0, v_cls_356_);
lean_ctor_set(v_data_406_, 1, v___x_404_);
lean_ctor_set(v_data_406_, 2, v_tag_358_);
lean_ctor_set_float(v_data_406_, sizeof(void*)*3, v___x_405_);
lean_ctor_set_float(v_data_406_, sizeof(void*)*3 + 8, v___x_405_);
lean_ctor_set_uint8(v_data_406_, sizeof(void*)*3 + 16, v_collapsed_357_);
if (v___x_398_ == 0)
{
lean_dec_ref_known(v___x_404_, 1);
lean_dec(v_snd_396_);
lean_dec(v_fst_395_);
lean_dec_ref(v_tag_358_);
lean_dec(v_cls_356_);
v___y_382_ = v___y_400_;
v___y_383_ = v_a_401_;
v_data_384_ = v_data_406_;
goto v___jp_381_;
}
else
{
lean_object* v_data_407_; double v___x_408_; double v___x_409_; 
lean_dec_ref_known(v_data_406_, 3);
v_data_407_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_407_, 0, v_cls_356_);
lean_ctor_set(v_data_407_, 1, v___x_404_);
lean_ctor_set(v_data_407_, 2, v_tag_358_);
v___x_408_ = lean_unbox_float(v_fst_395_);
lean_dec(v_fst_395_);
lean_ctor_set_float(v_data_407_, sizeof(void*)*3, v___x_408_);
v___x_409_ = lean_unbox_float(v_snd_396_);
lean_dec(v_snd_396_);
lean_ctor_set_float(v_data_407_, sizeof(void*)*3 + 8, v___x_409_);
lean_ctor_set_uint8(v_data_407_, sizeof(void*)*3 + 16, v_collapsed_357_);
v___y_382_ = v___y_400_;
v___y_383_ = v_a_401_;
v_data_384_ = v_data_407_;
goto v___jp_381_;
}
}
v___jp_410_:
{
lean_object* v_ref_411_; lean_object* v___x_412_; 
v_ref_411_ = lean_ctor_get(v___y_376_, 2);
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
lean_inc(v___y_369_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v_fst_379_);
v___x_412_ = lean_apply_16(v_msg_362_, v_fst_379_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, lean_box(0));
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___y_400_ = v_ref_411_;
v_a_401_ = v_a_413_;
goto v___jp_399_;
}
else
{
lean_object* v___x_414_; 
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2);
v___y_400_ = v_ref_411_;
v_a_401_ = v___x_414_;
goto v___jp_399_;
}
}
v___jp_415_:
{
if (v_clsEnabled_360_ == 0)
{
if (v___y_416_ == 0)
{
lean_object* v___x_417_; lean_object* v_traceState_418_; lean_object* v_env_419_; lean_object* v_nextMacroScope_420_; lean_object* v_ngen_421_; lean_object* v_auxDeclNGen_422_; lean_object* v_cache_423_; lean_object* v_recordedDeps_424_; lean_object* v_messages_425_; lean_object* v_infoState_426_; lean_object* v_snapshotTasks_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_snd_396_);
lean_dec(v_fst_395_);
lean_dec_ref(v_msg_362_);
lean_dec_ref(v_tag_358_);
lean_dec(v_cls_356_);
v___x_417_ = lean_st_ref_take(v___y_377_);
v_traceState_418_ = lean_ctor_get(v___x_417_, 4);
v_env_419_ = lean_ctor_get(v___x_417_, 0);
v_nextMacroScope_420_ = lean_ctor_get(v___x_417_, 1);
v_ngen_421_ = lean_ctor_get(v___x_417_, 2);
v_auxDeclNGen_422_ = lean_ctor_get(v___x_417_, 3);
v_cache_423_ = lean_ctor_get(v___x_417_, 5);
v_recordedDeps_424_ = lean_ctor_get(v___x_417_, 6);
v_messages_425_ = lean_ctor_get(v___x_417_, 7);
v_infoState_426_ = lean_ctor_get(v___x_417_, 8);
v_snapshotTasks_427_ = lean_ctor_get(v___x_417_, 9);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_446_ == 0)
{
v___x_429_ = v___x_417_;
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snapshotTasks_427_);
lean_inc(v_infoState_426_);
lean_inc(v_messages_425_);
lean_inc(v_recordedDeps_424_);
lean_inc(v_cache_423_);
lean_inc(v_traceState_418_);
lean_inc(v_auxDeclNGen_422_);
lean_inc(v_ngen_421_);
lean_inc(v_nextMacroScope_420_);
lean_inc(v_env_419_);
lean_dec(v___x_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint64_t v_tid_431_; lean_object* v_traces_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_445_; 
v_tid_431_ = lean_ctor_get_uint64(v_traceState_418_, sizeof(void*)*1);
v_traces_432_ = lean_ctor_get(v_traceState_418_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_traceState_418_);
if (v_isSharedCheck_445_ == 0)
{
v___x_434_ = v_traceState_418_;
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_traces_432_);
lean_dec(v_traceState_418_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_361_, v_traces_432_);
lean_dec_ref(v_traces_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_436_);
lean_ctor_set_uint64(v_reuseFailAlloc_444_, sizeof(void*)*1, v_tid_431_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 4, v___x_438_);
v___x_440_ = v___x_429_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_env_419_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_nextMacroScope_420_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_ngen_421_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_auxDeclNGen_422_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_cache_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_recordedDeps_424_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_messages_425_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_infoState_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 9, v_snapshotTasks_427_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_st_ref_put(v___y_377_, v___x_440_);
v___x_442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_379_);
return v___x_442_;
}
}
}
}
}
else
{
goto v___jp_410_;
}
}
else
{
goto v___jp_410_;
}
}
v___jp_447_:
{
double v___x_449_; double v___x_450_; double v___x_451_; uint8_t v___x_452_; 
v___x_449_ = lean_unbox_float(v_snd_396_);
v___x_450_ = lean_unbox_float(v_fst_395_);
v___x_451_ = lean_float_sub(v___x_449_, v___x_450_);
v___x_452_ = lean_float_decLt(v___y_448_, v___x_451_);
v___y_416_ = v___x_452_;
goto v___jp_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object** _args){
lean_object* v_cls_463_ = _args[0];
lean_object* v_collapsed_464_ = _args[1];
lean_object* v_tag_465_ = _args[2];
lean_object* v_opts_466_ = _args[3];
lean_object* v_clsEnabled_467_ = _args[4];
lean_object* v_oldTraces_468_ = _args[5];
lean_object* v_msg_469_ = _args[6];
lean_object* v_resStartStop_470_ = _args[7];
lean_object* v___y_471_ = _args[8];
lean_object* v___y_472_ = _args[9];
lean_object* v___y_473_ = _args[10];
lean_object* v___y_474_ = _args[11];
lean_object* v___y_475_ = _args[12];
lean_object* v___y_476_ = _args[13];
lean_object* v___y_477_ = _args[14];
lean_object* v___y_478_ = _args[15];
lean_object* v___y_479_ = _args[16];
lean_object* v___y_480_ = _args[17];
lean_object* v___y_481_ = _args[18];
lean_object* v___y_482_ = _args[19];
lean_object* v___y_483_ = _args[20];
lean_object* v___y_484_ = _args[21];
lean_object* v___y_485_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_486_; uint8_t v_clsEnabled_boxed_487_; lean_object* v_res_488_; 
v_collapsed_boxed_486_ = lean_unbox(v_collapsed_464_);
v_clsEnabled_boxed_487_ = lean_unbox(v_clsEnabled_467_);
v_res_488_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_cls_463_, v_collapsed_boxed_486_, v_tag_465_, v_opts_466_, v_clsEnabled_boxed_487_, v_oldTraces_468_, v_msg_469_, v_resStartStop_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec_ref(v_opts_466_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
return v_bs_491_;
}
else
{
lean_object* v_v_493_; lean_object* v_hyp_494_; lean_object* v___x_495_; lean_object* v_bs_x27_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_v_493_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
v_hyp_494_ = lean_ctor_get(v_v_493_, 0);
lean_inc_ref(v_hyp_494_);
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_495_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_490_, v___x_497_);
v___x_499_ = lean_array_uset(v_bs_x27_496_, v_i_490_, v_hyp_494_);
v_i_490_ = v___x_498_;
v_bs_491_ = v___x_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_505_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_boxed_504_, v_i_boxed_505_, v_bs_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_ref_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_ref_513_ = lean_ctor_get(v___y_510_, 2);
v___x_514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_inc(v_ref_513_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_ref_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object* v_as_538_, size_t v_sz_539_, size_t v_i_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_a_558_; uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_lt(v_i_540_, v_sz_539_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_b_541_);
return v___x_563_;
}
else
{
lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_a_564_ = lean_array_uget_borrowed(v_as_538_, v_i_540_);
v___x_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0));
v___x_566_ = l_Lean_Core_checkSystem(v___x_565_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_type_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
lean_dec_ref_known(v___x_566_, 1);
v_type_567_ = lean_ctor_get(v_a_564_, 1);
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2));
v___x_569_ = l_Lean_Expr_isConstOf(v_type_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v___y_544_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; 
lean_dec_ref_known(v___x_570_, 1);
lean_inc(v_a_564_);
v___x_571_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_a_564_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_574_; 
v_val_573_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_a_572_, 1);
v___x_574_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v___y_544_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = l_Array_append___redArg(v_b_541_, v_a_575_);
lean_dec(v_a_575_);
v___x_577_ = lean_array_push(v___x_576_, v_val_573_);
v_a_558_ = v___x_577_;
goto v___jp_557_;
}
else
{
lean_dec(v_val_573_);
lean_dec_ref(v_b_541_);
return v___x_574_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_a_572_);
v___x_578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4);
lean_inc_ref(v_type_567_);
v___x_579_ = l_Lean_MessageData_ofExpr(v_type_567_);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v___x_580_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_dec_ref_known(v___x_581_, 1);
v_a_558_ = v_b_541_;
goto v___jp_557_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_b_541_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_b_541_);
v_a_590_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_571_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_571_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_b_541_);
v_a_598_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_570_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_570_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
v_a_558_ = v_b_541_;
goto v___jp_557_;
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_b_541_);
v_a_606_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_566_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_566_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
v___jp_557_:
{
size_t v___x_559_; size_t v___x_560_; 
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_540_, v___x_559_);
v_i_540_ = v___x_560_;
v_b_541_ = v_a_558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object** _args){
lean_object* v_as_614_ = _args[0];
lean_object* v_sz_615_ = _args[1];
lean_object* v_i_616_ = _args[2];
lean_object* v_b_617_ = _args[3];
lean_object* v___y_618_ = _args[4];
lean_object* v___y_619_ = _args[5];
lean_object* v___y_620_ = _args[6];
lean_object* v___y_621_ = _args[7];
lean_object* v___y_622_ = _args[8];
lean_object* v___y_623_ = _args[9];
lean_object* v___y_624_ = _args[10];
lean_object* v___y_625_ = _args[11];
lean_object* v___y_626_ = _args[12];
lean_object* v___y_627_ = _args[13];
lean_object* v___y_628_ = _args[14];
lean_object* v___y_629_ = _args[15];
lean_object* v___y_630_ = _args[16];
lean_object* v___y_631_ = _args[17];
lean_object* v___y_632_ = _args[18];
_start:
{
size_t v_sz_boxed_633_; size_t v_i_boxed_634_; lean_object* v_res_635_; 
v_sz_boxed_633_ = lean_unbox_usize(v_sz_615_);
lean_dec(v_sz_615_);
v_i_boxed_634_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_614_, v_sz_boxed_633_, v_i_boxed_634_, v_b_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_as_614_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
lean_inc(v___x_648_);
v___x_649_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_639_, v___x_648_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; size_t v___x_651_; size_t v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_637_, v___x_651_);
v_i_637_ = v___x_652_;
v_b_639_ = v_a_650_;
goto _start;
}
else
{
return v___x_649_;
}
}
else
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_b_639_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg___boxed(lean_object* v_as_655_, lean_object* v_i_656_, lean_object* v_stop_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
size_t v_i_boxed_666_; size_t v_stop_boxed_667_; lean_object* v_res_668_; 
v_i_boxed_666_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_stop_boxed_667_ = lean_unbox_usize(v_stop_657_);
lean_dec(v_stop_657_);
v_res_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_655_, v_i_boxed_666_, v_stop_boxed_667_, v_b_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v_as_655_);
return v_res_668_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1(void){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2);
v___x_676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
lean_ctor_set(v___x_676_, 2, v___x_675_);
lean_ctor_set(v___x_676_, 3, v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_unsigned_to_nat(16u);
v___x_679_ = lean_mk_array(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
v___x_684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_ctor_set(v___x_684_, 2, v___x_683_);
lean_ctor_set(v___x_684_, 3, v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_702_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16));
v___x_703_ = l_Lean_Name_append(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18(void){
_start:
{
lean_object* v___x_704_; double v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(1000000000u);
v___x_705_ = lean_float_of_nat(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___y_722_; lean_object* v_a_723_; lean_object* v_hypQueue_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v_toCold_927_; lean_object* v_options_928_; uint8_t v_hasTrace_929_; 
v_toCold_927_ = lean_ctor_get(v_a_718_, 0);
v_options_928_ = lean_ctor_get(v_toCold_927_, 2);
v_hasTrace_929_ = lean_ctor_get_uint8(v_options_928_, sizeof(void*)*1);
if (v_hasTrace_929_ == 0)
{
lean_object* v___x_930_; lean_object* v_satExpr_931_; lean_object* v_hypQueue_932_; lean_object* v_usedHyps_933_; uint8_t v_didChange_934_; lean_object* v_theoryState_935_; lean_object* v_solverTimeBudgetMs_936_; lean_object* v_roundBudget_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v___x_930_ = lean_st_ref_take(v_a_707_);
v_satExpr_931_ = lean_ctor_get(v___x_930_, 0);
v_hypQueue_932_ = lean_ctor_get(v___x_930_, 1);
v_usedHyps_933_ = lean_ctor_get(v___x_930_, 2);
v_didChange_934_ = lean_ctor_get_uint8(v___x_930_, sizeof(void*)*6);
v_theoryState_935_ = lean_ctor_get(v___x_930_, 3);
v_solverTimeBudgetMs_936_ = lean_ctor_get(v___x_930_, 4);
v_roundBudget_937_ = lean_ctor_get(v___x_930_, 5);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v___x_930_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_roundBudget_937_);
lean_inc(v_solverTimeBudgetMs_936_);
lean_inc(v_theoryState_935_);
lean_inc(v_usedHyps_933_);
lean_inc(v_hypQueue_932_);
lean_inc(v_satExpr_931_);
lean_dec(v___x_930_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_942_ = l_Array_append___redArg(v_usedHyps_933_, v_hypQueue_932_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 2, v___x_942_);
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_satExpr_931_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_theoryState_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_solverTimeBudgetMs_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_roundBudget_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*6, v_didChange_934_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_st_ref_put(v_a_707_, v___x_944_);
v_hypQueue_744_ = v_hypQueue_932_;
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
v___y_758_ = v_a_719_;
goto v___jp_743_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v_a_957_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_a_972_; lean_object* v___y_975_; lean_object* v___y_976_; uint8_t v_a_977_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v_a_983_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v_a_1004_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v_a_1016_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v_a_1021_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v_a_1027_; 
v_inheritedTraceOptions_948_ = lean_ctor_get(v_toCold_927_, 11);
v___f_949_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_952_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_948_, v_options_928_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = l_Lean_trace_profiler;
v___x_1355_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_928_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v_satExpr_1357_; lean_object* v_hypQueue_1358_; lean_object* v_usedHyps_1359_; uint8_t v_didChange_1360_; lean_object* v_theoryState_1361_; lean_object* v_solverTimeBudgetMs_1362_; lean_object* v_roundBudget_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1373_; 
v___x_1356_ = lean_st_ref_take(v_a_707_);
v_satExpr_1357_ = lean_ctor_get(v___x_1356_, 0);
v_hypQueue_1358_ = lean_ctor_get(v___x_1356_, 1);
v_usedHyps_1359_ = lean_ctor_get(v___x_1356_, 2);
v_didChange_1360_ = lean_ctor_get_uint8(v___x_1356_, sizeof(void*)*6);
v_theoryState_1361_ = lean_ctor_get(v___x_1356_, 3);
v_solverTimeBudgetMs_1362_ = lean_ctor_get(v___x_1356_, 4);
v_roundBudget_1363_ = lean_ctor_get(v___x_1356_, 5);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1365_ = v___x_1356_;
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_roundBudget_1363_);
lean_inc(v_solverTimeBudgetMs_1362_);
lean_inc(v_theoryState_1361_);
lean_inc(v_usedHyps_1359_);
lean_inc(v_hypQueue_1358_);
lean_inc(v_satExpr_1357_);
lean_dec(v___x_1356_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1368_ = l_Array_append___redArg(v_usedHyps_1359_, v_hypQueue_1358_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1368_);
lean_ctor_set(v___x_1365_, 1, v___x_1367_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_satExpr_1357_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_theoryState_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_solverTimeBudgetMs_1362_);
lean_ctor_set(v_reuseFailAlloc_1372_, 5, v_roundBudget_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*6, v_didChange_1360_);
v___x_1370_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_st_ref_put(v_a_707_, v___x_1370_);
v_hypQueue_744_ = v_hypQueue_1358_;
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
v___y_758_ = v_a_719_;
goto v___jp_743_;
}
}
}
else
{
goto v___jp_1045_;
}
}
else
{
goto v___jp_1045_;
}
v___jp_954_:
{
lean_object* v___x_958_; double v___x_959_; double v___x_960_; double v___x_961_; double v___x_962_; double v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_958_ = lean_io_mono_nanos_now();
v___x_959_ = lean_float_of_nat(v___y_956_);
v___x_960_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
v___x_961_ = lean_float_div(v___x_959_, v___x_960_);
v___x_962_ = lean_float_of_nat(v___x_958_);
v___x_963_ = lean_float_div(v___x_962_, v___x_960_);
v___x_964_ = lean_box_float(v___x_961_);
v___x_965_ = lean_box_float(v___x_963_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_a_957_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_950_, v_hasTrace_929_, v___x_951_, v_options_928_, v___x_953_, v___y_955_, v___f_949_, v___x_967_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_968_;
}
v___jp_969_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_a_972_);
v___y_955_ = v___y_970_;
v___y_956_ = v___y_971_;
v_a_957_ = v___x_973_;
goto v___jp_954_;
}
v___jp_974_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_box(v_a_977_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___y_955_ = v___y_975_;
v___y_956_ = v___y_976_;
v_a_957_ = v___x_979_;
goto v___jp_954_;
}
v___jp_980_:
{
lean_object* v___x_984_; lean_object* v_hypQueue_985_; lean_object* v_usedHyps_986_; uint8_t v_didChange_987_; lean_object* v_theoryState_988_; lean_object* v_solverTimeBudgetMs_989_; lean_object* v_roundBudget_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v___x_984_ = lean_st_ref_take(v_a_707_);
v_hypQueue_985_ = lean_ctor_get(v___x_984_, 1);
v_usedHyps_986_ = lean_ctor_get(v___x_984_, 2);
v_didChange_987_ = lean_ctor_get_uint8(v___x_984_, sizeof(void*)*6);
v_theoryState_988_ = lean_ctor_get(v___x_984_, 3);
v_solverTimeBudgetMs_989_ = lean_ctor_get(v___x_984_, 4);
v_roundBudget_990_ = lean_ctor_get(v___x_984_, 5);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_984_, 0);
lean_dec(v_unused_1000_);
v___x_992_ = v___x_984_;
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_roundBudget_990_);
lean_inc(v_solverTimeBudgetMs_989_);
lean_inc(v_theoryState_988_);
lean_inc(v_usedHyps_986_);
lean_inc(v_hypQueue_985_);
lean_dec(v___x_984_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_a_983_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_hypQueue_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_usedHyps_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_theoryState_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_solverTimeBudgetMs_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_roundBudget_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*6, v_didChange_987_);
v___x_995_ = v_reuseFailAlloc_998_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_st_ref_put(v_a_707_, v___x_995_);
v___x_997_ = 1;
v___y_975_ = v___y_981_;
v___y_976_ = v___y_982_;
v_a_977_ = v___x_997_;
goto v___jp_974_;
}
}
}
v___jp_1001_:
{
lean_object* v___x_1005_; double v___x_1006_; double v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1005_ = lean_io_get_num_heartbeats();
v___x_1006_ = lean_float_of_nat(v___y_1003_);
v___x_1007_ = lean_float_of_nat(v___x_1005_);
v___x_1008_ = lean_box_float(v___x_1006_);
v___x_1009_ = lean_box_float(v___x_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_a_1004_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_950_, v_hasTrace_929_, v___x_951_, v_options_928_, v___x_953_, v___y_1002_, v___f_949_, v___x_1011_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_1012_;
}
v___jp_1013_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_a_1016_);
v___y_1002_ = v___y_1014_;
v___y_1003_ = v___y_1015_;
v_a_1004_ = v___x_1017_;
goto v___jp_1001_;
}
v___jp_1018_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_box(v_a_1021_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
v___y_1002_ = v___y_1019_;
v___y_1003_ = v___y_1020_;
v_a_1004_ = v___x_1023_;
goto v___jp_1001_;
}
v___jp_1024_:
{
lean_object* v___x_1028_; lean_object* v_hypQueue_1029_; lean_object* v_usedHyps_1030_; uint8_t v_didChange_1031_; lean_object* v_theoryState_1032_; lean_object* v_solverTimeBudgetMs_1033_; lean_object* v_roundBudget_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v___x_1028_ = lean_st_ref_take(v_a_707_);
v_hypQueue_1029_ = lean_ctor_get(v___x_1028_, 1);
v_usedHyps_1030_ = lean_ctor_get(v___x_1028_, 2);
v_didChange_1031_ = lean_ctor_get_uint8(v___x_1028_, sizeof(void*)*6);
v_theoryState_1032_ = lean_ctor_get(v___x_1028_, 3);
v_solverTimeBudgetMs_1033_ = lean_ctor_get(v___x_1028_, 4);
v_roundBudget_1034_ = lean_ctor_get(v___x_1028_, 5);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1044_);
v___x_1036_ = v___x_1028_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_roundBudget_1034_);
lean_inc(v_solverTimeBudgetMs_1033_);
lean_inc(v_theoryState_1032_);
lean_inc(v_usedHyps_1030_);
lean_inc(v_hypQueue_1029_);
lean_dec(v___x_1028_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_a_1027_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_hypQueue_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_usedHyps_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_theoryState_1032_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_solverTimeBudgetMs_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_roundBudget_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*6, v_didChange_1031_);
v___x_1039_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_st_ref_put(v_a_707_, v___x_1039_);
v___x_1041_ = 1;
v___y_1019_ = v___y_1025_;
v___y_1020_ = v___y_1026_;
v_a_1021_ = v___x_1041_;
goto v___jp_1018_;
}
}
}
v___jp_1045_:
{
lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1353_; 
v___x_1046_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v_a_719_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1353_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1353_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1052_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_928_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_satExpr_1055_; lean_object* v_hypQueue_1056_; lean_object* v_usedHyps_1057_; uint8_t v_didChange_1058_; lean_object* v_theoryState_1059_; lean_object* v_solverTimeBudgetMs_1060_; lean_object* v_roundBudget_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1202_; 
v___x_1053_ = lean_io_mono_nanos_now();
v___x_1054_ = lean_st_ref_take(v_a_707_);
v_satExpr_1055_ = lean_ctor_get(v___x_1054_, 0);
v_hypQueue_1056_ = lean_ctor_get(v___x_1054_, 1);
v_usedHyps_1057_ = lean_ctor_get(v___x_1054_, 2);
v_didChange_1058_ = lean_ctor_get_uint8(v___x_1054_, sizeof(void*)*6);
v_theoryState_1059_ = lean_ctor_get(v___x_1054_, 3);
v_solverTimeBudgetMs_1060_ = lean_ctor_get(v___x_1054_, 4);
v_roundBudget_1061_ = lean_ctor_get(v___x_1054_, 5);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1063_ = v___x_1054_;
v_isShared_1064_ = v_isSharedCheck_1202_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_roundBudget_1061_);
lean_inc(v_solverTimeBudgetMs_1060_);
lean_inc(v_theoryState_1059_);
lean_inc(v_usedHyps_1057_);
lean_inc(v_hypQueue_1056_);
lean_inc(v_satExpr_1055_);
lean_dec(v___x_1054_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1202_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1067_ = l_Array_append___redArg(v_usedHyps_1057_, v_hypQueue_1056_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 2, v___x_1067_);
lean_ctor_set(v___x_1063_, 1, v___x_1066_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_satExpr_1055_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_theoryState_1059_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_solverTimeBudgetMs_1060_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v_roundBudget_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1201_, sizeof(void*)*6, v_didChange_1058_);
v___x_1069_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_st_ref_put(v_a_707_, v___x_1069_);
v___x_1071_ = lean_array_get_size(v_hypQueue_1056_);
v___x_1072_ = lean_nat_dec_eq(v___x_1071_, v___x_1065_);
if (v___x_1072_ == 0)
{
lean_object* v_goal_1073_; lean_object* v_tacticContext_1074_; lean_object* v___x_1075_; lean_object* v_config_1076_; lean_object* v_mode_1077_; lean_object* v_timeout_1078_; uint8_t v_trimProofs_1079_; uint8_t v_binaryProofs_1080_; uint8_t v_acNf_1081_; uint8_t v_andFlattening_1082_; uint8_t v_embeddedConstraintSubst_1083_; uint8_t v_graphviz_1084_; lean_object* v_maxSteps_1085_; uint8_t v_solverMode_1086_; uint8_t v_uf_1087_; lean_object* v_cegarRounds_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1199_; 
v_goal_1073_ = lean_ctor_get(v_a_706_, 0);
v_tacticContext_1074_ = lean_ctor_get(v_a_706_, 2);
lean_inc_ref(v_tacticContext_1074_);
v___x_1075_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1074_);
v_config_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_config_1076_);
v_mode_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_mode_1077_);
lean_dec_ref(v___x_1075_);
v_timeout_1078_ = lean_ctor_get(v_config_1076_, 0);
v_trimProofs_1079_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3);
v_binaryProofs_1080_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 1);
v_acNf_1081_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 2);
v_andFlattening_1082_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1083_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 4);
v_graphviz_1084_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 8);
v_maxSteps_1085_ = lean_ctor_get(v_config_1076_, 1);
v_solverMode_1086_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 10);
v_uf_1087_ = lean_ctor_get_uint8(v_config_1076_, sizeof(void*)*3 + 11);
v_cegarRounds_1088_ = lean_ctor_get(v_config_1076_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_config_1076_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1090_ = v_config_1076_;
v_isShared_1091_ = v_isSharedCheck_1199_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_cegarRounds_1088_);
lean_inc(v_maxSteps_1085_);
lean_inc(v_timeout_1078_);
lean_dec(v_config_1076_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1199_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
lean_inc(v_goal_1073_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_goal_1073_);
v___x_1093_ = v___x_1049_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_goal_1073_);
v___x_1093_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1091_ == 0)
{
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_timeout_1078_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_maxSteps_1085_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_cegarRounds_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3, v_trimProofs_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 1, v_binaryProofs_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 2, v_acNf_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 3, v_andFlattening_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 8, v_graphviz_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 10, v_solverMode_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*3 + 11, v_uf_1087_);
v___x_1095_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_theoryState_1100_; lean_object* v_satExpr_1101_; lean_object* v_hypQueue_1102_; lean_object* v_usedHyps_1103_; uint8_t v_didChange_1104_; lean_object* v_solverTimeBudgetMs_1105_; lean_object* v_roundBudget_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1196_; 
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 5, v___x_1072_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 6, v___x_1072_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 7, v___x_1072_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 9, v___x_1072_);
v___x_1096_ = lean_box(v_hasTrace_929_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
v___x_1098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1077_, v___x_1095_, v___x_1097_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = lean_st_ref_take(v_a_707_);
v_theoryState_1100_ = lean_ctor_get(v___x_1099_, 3);
v_satExpr_1101_ = lean_ctor_get(v___x_1099_, 0);
v_hypQueue_1102_ = lean_ctor_get(v___x_1099_, 1);
v_usedHyps_1103_ = lean_ctor_get(v___x_1099_, 2);
v_didChange_1104_ = lean_ctor_get_uint8(v___x_1099_, sizeof(void*)*6);
v_solverTimeBudgetMs_1105_ = lean_ctor_get(v___x_1099_, 4);
v_roundBudget_1106_ = lean_ctor_get(v___x_1099_, 5);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1108_ = v___x_1099_;
v_isShared_1109_ = v_isSharedCheck_1196_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_roundBudget_1106_);
lean_inc(v_solverTimeBudgetMs_1105_);
lean_inc(v_theoryState_1100_);
lean_inc(v_usedHyps_1103_);
lean_inc(v_hypQueue_1102_);
lean_inc(v_satExpr_1101_);
lean_dec(v___x_1099_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1196_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_funState_1110_; lean_object* v_bitvecState_1111_; lean_object* v_preprocessCaches_1112_; lean_object* v_satSolver_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1195_; 
v_funState_1110_ = lean_ctor_get(v_theoryState_1100_, 0);
v_bitvecState_1111_ = lean_ctor_get(v_theoryState_1100_, 1);
v_preprocessCaches_1112_ = lean_ctor_get(v_theoryState_1100_, 2);
v_satSolver_1113_ = lean_ctor_get(v_theoryState_1100_, 3);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_theoryState_1100_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1115_ = v_theoryState_1100_;
v_isShared_1116_ = v_isSharedCheck_1195_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_satSolver_1113_);
lean_inc(v_preprocessCaches_1112_);
lean_inc(v_bitvecState_1111_);
lean_inc(v_funState_1110_);
lean_dec(v_theoryState_1100_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1195_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 2, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_funState_1110_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_bitvecState_1111_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_satSolver_1113_);
v___x_1119_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v___x_1119_);
v___x_1121_ = v___x_1108_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_satExpr_1101_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_hypQueue_1102_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_usedHyps_1103_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_solverTimeBudgetMs_1105_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_roundBudget_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*6, v_didChange_1104_);
v___x_1121_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_typeAnalysis_1127_; lean_object* v_target_1128_; lean_object* v_hypotheses_1129_; uint8_t v_didChange_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1191_; 
v___x_1122_ = lean_st_ref_put(v_a_707_, v___x_1121_);
v___x_1123_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1124_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1117_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_ctor_set(v___x_1124_, 2, v___x_1093_);
lean_ctor_set(v___x_1124_, 3, v___x_1066_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*4, v___x_1072_);
v___x_1125_ = lean_st_mk_ref(v___x_1124_);
v___x_1126_ = lean_st_ref_take(v___x_1125_);
v_typeAnalysis_1127_ = lean_ctor_get(v___x_1126_, 1);
v_target_1128_ = lean_ctor_get(v___x_1126_, 2);
v_hypotheses_1129_ = lean_ctor_get(v___x_1126_, 3);
v_didChange_1130_ = lean_ctor_get_uint8(v___x_1126_, sizeof(void*)*4);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1126_, 0);
lean_dec(v_unused_1192_);
v___x_1132_ = v___x_1126_;
v_isShared_1133_ = v_isSharedCheck_1191_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_hypotheses_1129_);
lean_inc(v_target_1128_);
lean_inc(v_typeAnalysis_1127_);
lean_dec(v___x_1126_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1191_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v_preprocessCaches_1112_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_preprocessCaches_1112_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_typeAnalysis_1127_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_target_1128_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_hypotheses_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, sizeof(void*)*4, v_didChange_1130_);
v___x_1135_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = lean_st_ref_put(v___x_1125_, v___x_1135_);
v_sz_1137_ = lean_array_size(v_hypQueue_1056_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1137_, v___x_1138_, v_hypQueue_1056_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
v___x_1141_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1140_, v___x_1098_, v___x_1125_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec_ref(v___x_1098_);
lean_dec_ref_known(v___x_1140_, 1);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_st_ref_get(v___x_1125_);
lean_dec(v___x_1125_);
v___x_1144_ = lean_unbox(v_a_1142_);
lean_dec(v_a_1142_);
if (v___x_1144_ == 0)
{
lean_object* v_caches_1145_; lean_object* v_hypotheses_1146_; lean_object* v___x_1147_; lean_object* v_theoryState_1148_; lean_object* v_satExpr_1149_; lean_object* v_hypQueue_1150_; lean_object* v_usedHyps_1151_; uint8_t v_didChange_1152_; lean_object* v_solverTimeBudgetMs_1153_; lean_object* v_roundBudget_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1187_; 
v_caches_1145_ = lean_ctor_get(v___x_1143_, 0);
lean_inc_ref(v_caches_1145_);
v_hypotheses_1146_ = lean_ctor_get(v___x_1143_, 3);
lean_inc_ref(v_hypotheses_1146_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_st_ref_take(v_a_707_);
v_theoryState_1148_ = lean_ctor_get(v___x_1147_, 3);
v_satExpr_1149_ = lean_ctor_get(v___x_1147_, 0);
v_hypQueue_1150_ = lean_ctor_get(v___x_1147_, 1);
v_usedHyps_1151_ = lean_ctor_get(v___x_1147_, 2);
v_didChange_1152_ = lean_ctor_get_uint8(v___x_1147_, sizeof(void*)*6);
v_solverTimeBudgetMs_1153_ = lean_ctor_get(v___x_1147_, 4);
v_roundBudget_1154_ = lean_ctor_get(v___x_1147_, 5);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1156_ = v___x_1147_;
v_isShared_1157_ = v_isSharedCheck_1187_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_roundBudget_1154_);
lean_inc(v_solverTimeBudgetMs_1153_);
lean_inc(v_theoryState_1148_);
lean_inc(v_usedHyps_1151_);
lean_inc(v_hypQueue_1150_);
lean_inc(v_satExpr_1149_);
lean_dec(v___x_1147_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1187_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_funState_1158_; lean_object* v_bitvecState_1159_; lean_object* v_satSolver_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1185_; 
v_funState_1158_ = lean_ctor_get(v_theoryState_1148_, 0);
v_bitvecState_1159_ = lean_ctor_get(v_theoryState_1148_, 1);
v_satSolver_1160_ = lean_ctor_get(v_theoryState_1148_, 3);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_theoryState_1148_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_theoryState_1148_, 2);
lean_dec(v_unused_1186_);
v___x_1162_ = v_theoryState_1148_;
v_isShared_1163_ = v_isSharedCheck_1185_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_satSolver_1160_);
lean_inc(v_bitvecState_1159_);
lean_inc(v_funState_1158_);
lean_dec(v_theoryState_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1185_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 2, v_caches_1145_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_funState_1158_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_bitvecState_1159_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_caches_1145_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_satSolver_1160_);
v___x_1165_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 3, v___x_1165_);
v___x_1167_ = v___x_1156_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_satExpr_1149_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_hypQueue_1150_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_usedHyps_1151_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_solverTimeBudgetMs_1153_);
lean_ctor_set(v_reuseFailAlloc_1183_, 5, v_roundBudget_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1183_, sizeof(void*)*6, v_didChange_1152_);
v___x_1167_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; size_t v_sz_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_st_ref_put(v_a_707_, v___x_1167_);
v_sz_1169_ = lean_array_size(v_hypotheses_1146_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1146_, v_sz_1169_, v___x_1138_, v___x_1066_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec_ref(v_hypotheses_1146_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_array_get_size(v_a_1171_);
v___x_1173_ = lean_nat_dec_eq(v___x_1172_, v___x_1065_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v_satExpr_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_st_ref_get(v_a_707_);
v_satExpr_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc_ref(v_satExpr_1175_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_nat_dec_lt(v___x_1065_, v___x_1172_);
if (v___x_1176_ == 0)
{
lean_dec(v_a_1171_);
v___y_981_ = v_a_1047_;
v___y_982_ = v___x_1053_;
v_a_983_ = v_satExpr_1175_;
goto v___jp_980_;
}
else
{
size_t v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_usize_of_nat(v___x_1172_);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1171_, v___x_1138_, v___x_1177_, v_satExpr_1175_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_1171_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___y_981_ = v_a_1047_;
v___y_982_ = v___x_1053_;
v_a_983_ = v_a_1179_;
goto v___jp_980_;
}
else
{
lean_object* v_a_1180_; 
v_a_1180_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1178_, 1);
v___y_970_ = v_a_1047_;
v___y_971_ = v___x_1053_;
v_a_972_ = v_a_1180_;
goto v___jp_969_;
}
}
}
else
{
uint8_t v___x_1181_; 
lean_dec(v_a_1171_);
v___x_1181_ = 2;
v___y_975_ = v_a_1047_;
v___y_976_ = v___x_1053_;
v_a_977_ = v___x_1181_;
goto v___jp_974_;
}
}
else
{
lean_object* v_a_1182_; 
v_a_1182_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1170_, 1);
v___y_970_ = v_a_1047_;
v___y_971_ = v___x_1053_;
v_a_972_ = v_a_1182_;
goto v___jp_969_;
}
}
}
}
}
}
else
{
uint8_t v___x_1188_; 
lean_dec(v___x_1143_);
v___x_1188_ = 0;
v___y_975_ = v_a_1047_;
v___y_976_ = v___x_1053_;
v_a_977_ = v___x_1188_;
goto v___jp_974_;
}
}
else
{
lean_object* v_a_1189_; 
lean_dec(v___x_1125_);
v_a_1189_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1141_, 1);
v___y_970_ = v_a_1047_;
v___y_971_ = v___x_1053_;
v_a_972_ = v_a_1189_;
goto v___jp_969_;
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
uint8_t v___x_1200_; 
lean_dec_ref(v_hypQueue_1056_);
lean_del_object(v___x_1049_);
v___x_1200_ = 2;
v___y_975_ = v_a_1047_;
v___y_976_ = v___x_1053_;
v_a_977_ = v___x_1200_;
goto v___jp_974_;
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_satExpr_1205_; lean_object* v_hypQueue_1206_; lean_object* v_usedHyps_1207_; uint8_t v_didChange_1208_; lean_object* v_theoryState_1209_; lean_object* v_solverTimeBudgetMs_1210_; lean_object* v_roundBudget_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1352_; 
v___x_1203_ = lean_io_get_num_heartbeats();
v___x_1204_ = lean_st_ref_take(v_a_707_);
v_satExpr_1205_ = lean_ctor_get(v___x_1204_, 0);
v_hypQueue_1206_ = lean_ctor_get(v___x_1204_, 1);
v_usedHyps_1207_ = lean_ctor_get(v___x_1204_, 2);
v_didChange_1208_ = lean_ctor_get_uint8(v___x_1204_, sizeof(void*)*6);
v_theoryState_1209_ = lean_ctor_get(v___x_1204_, 3);
v_solverTimeBudgetMs_1210_ = lean_ctor_get(v___x_1204_, 4);
v_roundBudget_1211_ = lean_ctor_get(v___x_1204_, 5);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1213_ = v___x_1204_;
v_isShared_1214_ = v_isSharedCheck_1352_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_roundBudget_1211_);
lean_inc(v_solverTimeBudgetMs_1210_);
lean_inc(v_theoryState_1209_);
lean_inc(v_usedHyps_1207_);
lean_inc(v_hypQueue_1206_);
lean_inc(v_satExpr_1205_);
lean_dec(v___x_1204_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1352_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1217_ = l_Array_append___redArg(v_usedHyps_1207_, v_hypQueue_1206_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v___x_1217_);
lean_ctor_set(v___x_1213_, 1, v___x_1216_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_satExpr_1205_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_theoryState_1209_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_solverTimeBudgetMs_1210_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_roundBudget_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6, v_didChange_1208_);
v___x_1219_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_st_ref_put(v_a_707_, v___x_1219_);
v___x_1221_ = lean_array_get_size(v_hypQueue_1206_);
v___x_1222_ = lean_nat_dec_eq(v___x_1221_, v___x_1215_);
if (v___x_1222_ == 0)
{
lean_object* v_goal_1223_; lean_object* v_tacticContext_1224_; lean_object* v___x_1225_; lean_object* v_config_1226_; lean_object* v_mode_1227_; lean_object* v_timeout_1228_; uint8_t v_trimProofs_1229_; uint8_t v_binaryProofs_1230_; uint8_t v_acNf_1231_; uint8_t v_andFlattening_1232_; uint8_t v_embeddedConstraintSubst_1233_; uint8_t v_graphviz_1234_; lean_object* v_maxSteps_1235_; uint8_t v_solverMode_1236_; uint8_t v_uf_1237_; lean_object* v_cegarRounds_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1349_; 
v_goal_1223_ = lean_ctor_get(v_a_706_, 0);
v_tacticContext_1224_ = lean_ctor_get(v_a_706_, 2);
lean_inc_ref(v_tacticContext_1224_);
v___x_1225_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1224_);
v_config_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_config_1226_);
v_mode_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_mode_1227_);
lean_dec_ref(v___x_1225_);
v_timeout_1228_ = lean_ctor_get(v_config_1226_, 0);
v_trimProofs_1229_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3);
v_binaryProofs_1230_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 1);
v_acNf_1231_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 2);
v_andFlattening_1232_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1233_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 4);
v_graphviz_1234_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 8);
v_maxSteps_1235_ = lean_ctor_get(v_config_1226_, 1);
v_solverMode_1236_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 10);
v_uf_1237_ = lean_ctor_get_uint8(v_config_1226_, sizeof(void*)*3 + 11);
v_cegarRounds_1238_ = lean_ctor_get(v_config_1226_, 2);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_config_1226_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1240_ = v_config_1226_;
v_isShared_1241_ = v_isSharedCheck_1349_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_cegarRounds_1238_);
lean_inc(v_maxSteps_1235_);
lean_inc(v_timeout_1228_);
lean_dec(v_config_1226_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1349_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_goal_1223_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_goal_1223_);
v___x_1243_ = v___x_1049_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_goal_1223_);
v___x_1243_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1241_ == 0)
{
v___x_1245_ = v___x_1240_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_timeout_1228_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_maxSteps_1235_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_cegarRounds_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3, v_trimProofs_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 1, v_binaryProofs_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 2, v_acNf_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 3, v_andFlattening_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 8, v_graphviz_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 10, v_solverMode_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 11, v_uf_1237_);
v___x_1245_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_theoryState_1250_; lean_object* v_satExpr_1251_; lean_object* v_hypQueue_1252_; lean_object* v_usedHyps_1253_; uint8_t v_didChange_1254_; lean_object* v_solverTimeBudgetMs_1255_; lean_object* v_roundBudget_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1346_; 
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 5, v___x_1222_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 6, v___x_1222_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 7, v___x_1222_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 9, v___x_1222_);
v___x_1246_ = lean_box(v___x_1052_);
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
v___x_1248_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1227_, v___x_1245_, v___x_1247_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = lean_st_ref_take(v_a_707_);
v_theoryState_1250_ = lean_ctor_get(v___x_1249_, 3);
v_satExpr_1251_ = lean_ctor_get(v___x_1249_, 0);
v_hypQueue_1252_ = lean_ctor_get(v___x_1249_, 1);
v_usedHyps_1253_ = lean_ctor_get(v___x_1249_, 2);
v_didChange_1254_ = lean_ctor_get_uint8(v___x_1249_, sizeof(void*)*6);
v_solverTimeBudgetMs_1255_ = lean_ctor_get(v___x_1249_, 4);
v_roundBudget_1256_ = lean_ctor_get(v___x_1249_, 5);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1258_ = v___x_1249_;
v_isShared_1259_ = v_isSharedCheck_1346_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_roundBudget_1256_);
lean_inc(v_solverTimeBudgetMs_1255_);
lean_inc(v_theoryState_1250_);
lean_inc(v_usedHyps_1253_);
lean_inc(v_hypQueue_1252_);
lean_inc(v_satExpr_1251_);
lean_dec(v___x_1249_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1346_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_funState_1260_; lean_object* v_bitvecState_1261_; lean_object* v_preprocessCaches_1262_; lean_object* v_satSolver_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1345_; 
v_funState_1260_ = lean_ctor_get(v_theoryState_1250_, 0);
v_bitvecState_1261_ = lean_ctor_get(v_theoryState_1250_, 1);
v_preprocessCaches_1262_ = lean_ctor_get(v_theoryState_1250_, 2);
v_satSolver_1263_ = lean_ctor_get(v_theoryState_1250_, 3);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_theoryState_1250_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1265_ = v_theoryState_1250_;
v_isShared_1266_ = v_isSharedCheck_1345_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_satSolver_1263_);
lean_inc(v_preprocessCaches_1262_);
lean_inc(v_bitvecState_1261_);
lean_inc(v_funState_1260_);
lean_dec(v_theoryState_1250_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1345_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 2, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_funState_1260_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_bitvecState_1261_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_satSolver_1263_);
v___x_1269_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 3, v___x_1269_);
v___x_1271_ = v___x_1258_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_satExpr_1251_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_hypQueue_1252_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_usedHyps_1253_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_solverTimeBudgetMs_1255_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_roundBudget_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1343_, sizeof(void*)*6, v_didChange_1254_);
v___x_1271_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_typeAnalysis_1277_; lean_object* v_target_1278_; lean_object* v_hypotheses_1279_; uint8_t v_didChange_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1341_; 
v___x_1272_ = lean_st_ref_put(v_a_707_, v___x_1271_);
v___x_1273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1274_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1267_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
lean_ctor_set(v___x_1274_, 2, v___x_1243_);
lean_ctor_set(v___x_1274_, 3, v___x_1216_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*4, v___x_1222_);
v___x_1275_ = lean_st_mk_ref(v___x_1274_);
v___x_1276_ = lean_st_ref_take(v___x_1275_);
v_typeAnalysis_1277_ = lean_ctor_get(v___x_1276_, 1);
v_target_1278_ = lean_ctor_get(v___x_1276_, 2);
v_hypotheses_1279_ = lean_ctor_get(v___x_1276_, 3);
v_didChange_1280_ = lean_ctor_get_uint8(v___x_1276_, sizeof(void*)*4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1342_);
v___x_1282_ = v___x_1276_;
v_isShared_1283_ = v_isSharedCheck_1341_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_hypotheses_1279_);
lean_inc(v_target_1278_);
lean_inc(v_typeAnalysis_1277_);
lean_dec(v___x_1276_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1341_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_preprocessCaches_1262_);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_preprocessCaches_1262_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_typeAnalysis_1277_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_target_1278_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_hypotheses_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*4, v_didChange_1280_);
v___x_1285_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; size_t v_sz_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1286_ = lean_st_ref_put(v___x_1275_, v___x_1285_);
v_sz_1287_ = lean_array_size(v_hypQueue_1206_);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1287_, v___x_1288_, v_hypQueue_1206_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___x_1291_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1290_, v___x_1248_, v___x_1275_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec_ref(v___x_1248_);
lean_dec_ref_known(v___x_1290_, 1);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = lean_st_ref_get(v___x_1275_);
lean_dec(v___x_1275_);
v___x_1294_ = lean_unbox(v_a_1292_);
lean_dec(v_a_1292_);
if (v___x_1294_ == 0)
{
lean_object* v_caches_1295_; lean_object* v_hypotheses_1296_; lean_object* v___x_1297_; lean_object* v_theoryState_1298_; lean_object* v_satExpr_1299_; lean_object* v_hypQueue_1300_; lean_object* v_usedHyps_1301_; uint8_t v_didChange_1302_; lean_object* v_solverTimeBudgetMs_1303_; lean_object* v_roundBudget_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1337_; 
v_caches_1295_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_caches_1295_);
v_hypotheses_1296_ = lean_ctor_get(v___x_1293_, 3);
lean_inc_ref(v_hypotheses_1296_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_st_ref_take(v_a_707_);
v_theoryState_1298_ = lean_ctor_get(v___x_1297_, 3);
v_satExpr_1299_ = lean_ctor_get(v___x_1297_, 0);
v_hypQueue_1300_ = lean_ctor_get(v___x_1297_, 1);
v_usedHyps_1301_ = lean_ctor_get(v___x_1297_, 2);
v_didChange_1302_ = lean_ctor_get_uint8(v___x_1297_, sizeof(void*)*6);
v_solverTimeBudgetMs_1303_ = lean_ctor_get(v___x_1297_, 4);
v_roundBudget_1304_ = lean_ctor_get(v___x_1297_, 5);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1306_ = v___x_1297_;
v_isShared_1307_ = v_isSharedCheck_1337_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_roundBudget_1304_);
lean_inc(v_solverTimeBudgetMs_1303_);
lean_inc(v_theoryState_1298_);
lean_inc(v_usedHyps_1301_);
lean_inc(v_hypQueue_1300_);
lean_inc(v_satExpr_1299_);
lean_dec(v___x_1297_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1337_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_funState_1308_; lean_object* v_bitvecState_1309_; lean_object* v_satSolver_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1335_; 
v_funState_1308_ = lean_ctor_get(v_theoryState_1298_, 0);
v_bitvecState_1309_ = lean_ctor_get(v_theoryState_1298_, 1);
v_satSolver_1310_ = lean_ctor_get(v_theoryState_1298_, 3);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_theoryState_1298_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_theoryState_1298_, 2);
lean_dec(v_unused_1336_);
v___x_1312_ = v_theoryState_1298_;
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_satSolver_1310_);
lean_inc(v_bitvecState_1309_);
lean_inc(v_funState_1308_);
lean_dec(v_theoryState_1298_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v_caches_1295_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_funState_1308_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_bitvecState_1309_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_caches_1295_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_satSolver_1310_);
v___x_1315_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 3, v___x_1315_);
v___x_1317_ = v___x_1306_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_satExpr_1299_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_hypQueue_1300_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_usedHyps_1301_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_solverTimeBudgetMs_1303_);
lean_ctor_set(v_reuseFailAlloc_1333_, 5, v_roundBudget_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, sizeof(void*)*6, v_didChange_1302_);
v___x_1317_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; size_t v_sz_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_put(v_a_707_, v___x_1317_);
v_sz_1319_ = lean_array_size(v_hypotheses_1296_);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1296_, v_sz_1319_, v___x_1288_, v___x_1216_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec_ref(v_hypotheses_1296_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = lean_array_get_size(v_a_1321_);
v___x_1323_ = lean_nat_dec_eq(v___x_1322_, v___x_1215_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v_satExpr_1325_; uint8_t v___x_1326_; 
v___x_1324_ = lean_st_ref_get(v_a_707_);
v_satExpr_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_satExpr_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = lean_nat_dec_lt(v___x_1215_, v___x_1322_);
if (v___x_1326_ == 0)
{
lean_dec(v_a_1321_);
v___y_1025_ = v_a_1047_;
v___y_1026_ = v___x_1203_;
v_a_1027_ = v_satExpr_1325_;
goto v___jp_1024_;
}
else
{
size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_usize_of_nat(v___x_1322_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1321_, v___x_1288_, v___x_1327_, v_satExpr_1325_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_1321_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___y_1025_ = v_a_1047_;
v___y_1026_ = v___x_1203_;
v_a_1027_ = v_a_1329_;
goto v___jp_1024_;
}
else
{
lean_object* v_a_1330_; 
v_a_1330_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1328_, 1);
v___y_1014_ = v_a_1047_;
v___y_1015_ = v___x_1203_;
v_a_1016_ = v_a_1330_;
goto v___jp_1013_;
}
}
}
else
{
uint8_t v___x_1331_; 
lean_dec(v_a_1321_);
v___x_1331_ = 2;
v___y_1019_ = v_a_1047_;
v___y_1020_ = v___x_1203_;
v_a_1021_ = v___x_1331_;
goto v___jp_1018_;
}
}
else
{
lean_object* v_a_1332_; 
v_a_1332_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1320_, 1);
v___y_1014_ = v_a_1047_;
v___y_1015_ = v___x_1203_;
v_a_1016_ = v_a_1332_;
goto v___jp_1013_;
}
}
}
}
}
}
else
{
uint8_t v___x_1338_; 
lean_dec(v___x_1293_);
v___x_1338_ = 0;
v___y_1019_ = v_a_1047_;
v___y_1020_ = v___x_1203_;
v_a_1021_ = v___x_1338_;
goto v___jp_1018_;
}
}
else
{
lean_object* v_a_1339_; 
lean_dec(v___x_1275_);
v_a_1339_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1291_, 1);
v___y_1014_ = v_a_1047_;
v___y_1015_ = v___x_1203_;
v_a_1016_ = v_a_1339_;
goto v___jp_1013_;
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
uint8_t v___x_1350_; 
lean_dec_ref(v_hypQueue_1206_);
lean_del_object(v___x_1049_);
v___x_1350_ = 2;
v___y_1019_ = v_a_1047_;
v___y_1020_ = v___x_1203_;
v_a_1021_ = v___x_1350_;
goto v___jp_1018_;
}
}
}
}
}
}
}
v___jp_721_:
{
lean_object* v___x_724_; lean_object* v_hypQueue_725_; lean_object* v_usedHyps_726_; uint8_t v_didChange_727_; lean_object* v_theoryState_728_; lean_object* v_solverTimeBudgetMs_729_; lean_object* v_roundBudget_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_741_; 
v___x_724_ = lean_st_ref_take(v___y_722_);
v_hypQueue_725_ = lean_ctor_get(v___x_724_, 1);
v_usedHyps_726_ = lean_ctor_get(v___x_724_, 2);
v_didChange_727_ = lean_ctor_get_uint8(v___x_724_, sizeof(void*)*6);
v_theoryState_728_ = lean_ctor_get(v___x_724_, 3);
v_solverTimeBudgetMs_729_ = lean_ctor_get(v___x_724_, 4);
v_roundBudget_730_ = lean_ctor_get(v___x_724_, 5);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_724_, 0);
lean_dec(v_unused_742_);
v___x_732_ = v___x_724_;
v_isShared_733_ = v_isSharedCheck_741_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_roundBudget_730_);
lean_inc(v_solverTimeBudgetMs_729_);
lean_inc(v_theoryState_728_);
lean_inc(v_usedHyps_726_);
lean_inc(v_hypQueue_725_);
lean_dec(v___x_724_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_741_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v_a_723_);
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_723_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_hypQueue_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_usedHyps_726_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_theoryState_728_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_solverTimeBudgetMs_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 5, v_roundBudget_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_740_, sizeof(void*)*6, v_didChange_727_);
v___x_735_ = v_reuseFailAlloc_740_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = lean_st_ref_put(v___y_722_, v___x_735_);
v___x_737_ = 1;
v___x_738_ = lean_box(v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
}
v___jp_743_:
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_array_get_size(v_hypQueue_744_);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_nat_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v_goal_762_; lean_object* v_tacticContext_763_; lean_object* v___x_764_; lean_object* v_config_765_; lean_object* v_mode_766_; lean_object* v_timeout_767_; uint8_t v_trimProofs_768_; uint8_t v_binaryProofs_769_; uint8_t v_acNf_770_; uint8_t v_andFlattening_771_; uint8_t v_embeddedConstraintSubst_772_; uint8_t v_graphviz_773_; lean_object* v_maxSteps_774_; uint8_t v_solverMode_775_; uint8_t v_uf_776_; lean_object* v_cegarRounds_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_923_; 
v_goal_762_ = lean_ctor_get(v___y_745_, 0);
v_tacticContext_763_ = lean_ctor_get(v___y_745_, 2);
lean_inc_ref(v_tacticContext_763_);
v___x_764_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_763_);
v_config_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_config_765_);
v_mode_766_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_mode_766_);
lean_dec_ref(v___x_764_);
v_timeout_767_ = lean_ctor_get(v_config_765_, 0);
v_trimProofs_768_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3);
v_binaryProofs_769_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 1);
v_acNf_770_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 2);
v_andFlattening_771_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_772_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 4);
v_graphviz_773_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 8);
v_maxSteps_774_ = lean_ctor_get(v_config_765_, 1);
v_solverMode_775_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 10);
v_uf_776_ = lean_ctor_get_uint8(v_config_765_, sizeof(void*)*3 + 11);
v_cegarRounds_777_ = lean_ctor_get(v_config_765_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v_config_765_);
if (v_isSharedCheck_923_ == 0)
{
v___x_779_ = v_config_765_;
v_isShared_780_ = v_isSharedCheck_923_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_cegarRounds_777_);
lean_inc(v_maxSteps_774_);
lean_inc(v_timeout_767_);
lean_dec(v_config_765_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_923_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_inc(v_goal_762_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_goal_762_);
if (v_isShared_780_ == 0)
{
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_timeout_767_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_maxSteps_774_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_cegarRounds_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3, v_trimProofs_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 1, v_binaryProofs_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 2, v_acNf_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 3, v_andFlattening_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 8, v_graphviz_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 10, v_solverMode_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 11, v_uf_776_);
v___x_783_ = v_reuseFailAlloc_922_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_theoryState_787_; lean_object* v_satExpr_788_; lean_object* v_hypQueue_789_; lean_object* v_usedHyps_790_; uint8_t v_didChange_791_; lean_object* v_solverTimeBudgetMs_792_; lean_object* v_roundBudget_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_921_; 
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 5, v___x_761_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 6, v___x_761_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 7, v___x_761_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 9, v___x_761_);
v___x_784_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_785_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_766_, v___x_783_, v___x_784_);
v___x_786_ = lean_st_ref_take(v___y_746_);
v_theoryState_787_ = lean_ctor_get(v___x_786_, 3);
v_satExpr_788_ = lean_ctor_get(v___x_786_, 0);
v_hypQueue_789_ = lean_ctor_get(v___x_786_, 1);
v_usedHyps_790_ = lean_ctor_get(v___x_786_, 2);
v_didChange_791_ = lean_ctor_get_uint8(v___x_786_, sizeof(void*)*6);
v_solverTimeBudgetMs_792_ = lean_ctor_get(v___x_786_, 4);
v_roundBudget_793_ = lean_ctor_get(v___x_786_, 5);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_921_ == 0)
{
v___x_795_ = v___x_786_;
v_isShared_796_ = v_isSharedCheck_921_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_roundBudget_793_);
lean_inc(v_solverTimeBudgetMs_792_);
lean_inc(v_theoryState_787_);
lean_inc(v_usedHyps_790_);
lean_inc(v_hypQueue_789_);
lean_inc(v_satExpr_788_);
lean_dec(v___x_786_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_921_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_funState_797_; lean_object* v_bitvecState_798_; lean_object* v_preprocessCaches_799_; lean_object* v_satSolver_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_920_; 
v_funState_797_ = lean_ctor_get(v_theoryState_787_, 0);
v_bitvecState_798_ = lean_ctor_get(v_theoryState_787_, 1);
v_preprocessCaches_799_ = lean_ctor_get(v_theoryState_787_, 2);
v_satSolver_800_ = lean_ctor_get(v_theoryState_787_, 3);
v_isSharedCheck_920_ = !lean_is_exclusive(v_theoryState_787_);
if (v_isSharedCheck_920_ == 0)
{
v___x_802_ = v_theoryState_787_;
v_isShared_803_ = v_isSharedCheck_920_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_satSolver_800_);
lean_inc(v_preprocessCaches_799_);
lean_inc(v_bitvecState_798_);
lean_inc(v_funState_797_);
lean_dec(v_theoryState_787_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_920_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 2, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_funState_797_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_bitvecState_798_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_satSolver_800_);
v___x_806_ = v_reuseFailAlloc_919_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 3, v___x_806_);
v___x_808_ = v___x_795_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_satExpr_788_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_hypQueue_789_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_usedHyps_790_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_solverTimeBudgetMs_792_);
lean_ctor_set(v_reuseFailAlloc_918_, 5, v_roundBudget_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_918_, sizeof(void*)*6, v_didChange_791_);
v___x_808_ = v_reuseFailAlloc_918_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_typeAnalysis_815_; lean_object* v_target_816_; lean_object* v_hypotheses_817_; uint8_t v_didChange_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_916_; 
v___x_809_ = lean_st_ref_put(v___y_746_, v___x_808_);
v___x_810_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_811_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7));
v___x_812_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_812_, 0, v___x_804_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
lean_ctor_set(v___x_812_, 2, v___x_781_);
lean_ctor_set(v___x_812_, 3, v___x_811_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*4, v___x_761_);
v___x_813_ = lean_st_mk_ref(v___x_812_);
v___x_814_ = lean_st_ref_take(v___x_813_);
v_typeAnalysis_815_ = lean_ctor_get(v___x_814_, 1);
v_target_816_ = lean_ctor_get(v___x_814_, 2);
v_hypotheses_817_ = lean_ctor_get(v___x_814_, 3);
v_didChange_818_ = lean_ctor_get_uint8(v___x_814_, sizeof(void*)*4);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_814_, 0);
lean_dec(v_unused_917_);
v___x_820_ = v___x_814_;
v_isShared_821_ = v_isSharedCheck_916_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_hypotheses_817_);
lean_inc(v_target_816_);
lean_inc(v_typeAnalysis_815_);
lean_dec(v___x_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_916_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_preprocessCaches_799_);
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_preprocessCaches_799_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_typeAnalysis_815_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_target_816_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_hypotheses_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*4, v_didChange_818_);
v___x_823_ = v_reuseFailAlloc_915_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; size_t v_sz_825_; size_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_824_ = lean_st_ref_put(v___x_813_, v___x_823_);
v_sz_825_ = lean_array_size(v_hypQueue_744_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_825_, v___x_826_, v_hypQueue_744_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_828_, v___x_785_, v___x_813_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec_ref(v___x_785_);
lean_dec_ref_known(v___x_828_, 1);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_906_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_906_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_906_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_906_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_st_ref_get(v___x_813_);
lean_dec(v___x_813_);
v___x_835_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_835_ == 0)
{
lean_object* v_caches_836_; lean_object* v_hypotheses_837_; lean_object* v___x_838_; lean_object* v_theoryState_839_; lean_object* v_satExpr_840_; lean_object* v_hypQueue_841_; lean_object* v_usedHyps_842_; uint8_t v_didChange_843_; lean_object* v_solverTimeBudgetMs_844_; lean_object* v_roundBudget_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_900_; 
lean_del_object(v___x_832_);
v_caches_836_ = lean_ctor_get(v___x_834_, 0);
lean_inc_ref(v_caches_836_);
v_hypotheses_837_ = lean_ctor_get(v___x_834_, 3);
lean_inc_ref(v_hypotheses_837_);
lean_dec(v___x_834_);
v___x_838_ = lean_st_ref_take(v___y_746_);
v_theoryState_839_ = lean_ctor_get(v___x_838_, 3);
v_satExpr_840_ = lean_ctor_get(v___x_838_, 0);
v_hypQueue_841_ = lean_ctor_get(v___x_838_, 1);
v_usedHyps_842_ = lean_ctor_get(v___x_838_, 2);
v_didChange_843_ = lean_ctor_get_uint8(v___x_838_, sizeof(void*)*6);
v_solverTimeBudgetMs_844_ = lean_ctor_get(v___x_838_, 4);
v_roundBudget_845_ = lean_ctor_get(v___x_838_, 5);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_900_ == 0)
{
v___x_847_ = v___x_838_;
v_isShared_848_ = v_isSharedCheck_900_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_roundBudget_845_);
lean_inc(v_solverTimeBudgetMs_844_);
lean_inc(v_theoryState_839_);
lean_inc(v_usedHyps_842_);
lean_inc(v_hypQueue_841_);
lean_inc(v_satExpr_840_);
lean_dec(v___x_838_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_900_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_funState_849_; lean_object* v_bitvecState_850_; lean_object* v_satSolver_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_898_; 
v_funState_849_ = lean_ctor_get(v_theoryState_839_, 0);
v_bitvecState_850_ = lean_ctor_get(v_theoryState_839_, 1);
v_satSolver_851_ = lean_ctor_get(v_theoryState_839_, 3);
v_isSharedCheck_898_ = !lean_is_exclusive(v_theoryState_839_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_theoryState_839_, 2);
lean_dec(v_unused_899_);
v___x_853_ = v_theoryState_839_;
v_isShared_854_ = v_isSharedCheck_898_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_satSolver_851_);
lean_inc(v_bitvecState_850_);
lean_inc(v_funState_849_);
lean_dec(v_theoryState_839_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_898_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 2, v_caches_836_);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_funState_849_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_bitvecState_850_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_caches_836_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_satSolver_851_);
v___x_856_ = v_reuseFailAlloc_897_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 3, v___x_856_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_satExpr_840_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_hypQueue_841_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_usedHyps_842_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_solverTimeBudgetMs_844_);
lean_ctor_set(v_reuseFailAlloc_896_, 5, v_roundBudget_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_896_, sizeof(void*)*6, v_didChange_843_);
v___x_858_ = v_reuseFailAlloc_896_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; size_t v_sz_860_; lean_object* v___x_861_; 
v___x_859_ = lean_st_ref_put(v___y_746_, v___x_858_);
v_sz_860_ = lean_array_size(v_hypotheses_837_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_837_, v_sz_860_, v___x_826_, v___x_811_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec_ref(v_hypotheses_837_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_887_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_887_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_887_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_887_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_a_862_);
v___x_867_ = lean_nat_dec_eq(v___x_866_, v___x_760_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v_satExpr_869_; uint8_t v___x_870_; 
lean_del_object(v___x_864_);
v___x_868_ = lean_st_ref_get(v___y_746_);
v_satExpr_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc_ref(v_satExpr_869_);
lean_dec(v___x_868_);
v___x_870_ = lean_nat_dec_lt(v___x_760_, v___x_866_);
if (v___x_870_ == 0)
{
lean_dec(v_a_862_);
v___y_722_ = v___y_746_;
v_a_723_ = v_satExpr_869_;
goto v___jp_721_;
}
else
{
size_t v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_usize_of_nat(v___x_866_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_862_, v___x_826_, v___x_871_, v_satExpr_869_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v_a_862_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___y_722_ = v___y_746_;
v_a_723_ = v_a_873_;
goto v___jp_721_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_872_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_872_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
else
{
uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
lean_dec(v_a_862_);
v___x_882_ = 2;
v___x_883_ = lean_box(v___x_882_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_883_);
v___x_885_ = v___x_864_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_861_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_861_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
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
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v___x_834_);
v___x_901_ = 0;
v___x_902_ = lean_box(v___x_901_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_902_);
v___x_904_ = v___x_832_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___x_813_);
v_a_907_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_829_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_829_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
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
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_hypQueue_744_);
v___x_924_ = 2;
v___x_925_ = lean_box(v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1391_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1408_ = _args[0];
lean_object* v_msg_1409_ = _args[1];
lean_object* v___y_1410_ = _args[2];
lean_object* v___y_1411_ = _args[3];
lean_object* v___y_1412_ = _args[4];
lean_object* v___y_1413_ = _args[5];
lean_object* v___y_1414_ = _args[6];
lean_object* v___y_1415_ = _args[7];
lean_object* v___y_1416_ = _args[8];
lean_object* v___y_1417_ = _args[9];
lean_object* v___y_1418_ = _args[10];
lean_object* v___y_1419_ = _args[11];
lean_object* v___y_1420_ = _args[12];
lean_object* v___y_1421_ = _args[13];
lean_object* v___y_1422_ = _args[14];
lean_object* v___y_1423_ = _args[15];
lean_object* v___y_1424_ = _args[16];
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1408_, v_msg_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_1426_, size_t v_i_1427_, size_t v_stop_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_1426_, v_i_1427_, v_stop_1428_, v_b_1429_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object** _args){
lean_object* v_as_1446_ = _args[0];
lean_object* v_i_1447_ = _args[1];
lean_object* v_stop_1448_ = _args[2];
lean_object* v_b_1449_ = _args[3];
lean_object* v___y_1450_ = _args[4];
lean_object* v___y_1451_ = _args[5];
lean_object* v___y_1452_ = _args[6];
lean_object* v___y_1453_ = _args[7];
lean_object* v___y_1454_ = _args[8];
lean_object* v___y_1455_ = _args[9];
lean_object* v___y_1456_ = _args[10];
lean_object* v___y_1457_ = _args[11];
lean_object* v___y_1458_ = _args[12];
lean_object* v___y_1459_ = _args[13];
lean_object* v___y_1460_ = _args[14];
lean_object* v___y_1461_ = _args[15];
lean_object* v___y_1462_ = _args[16];
lean_object* v___y_1463_ = _args[17];
lean_object* v___y_1464_ = _args[18];
_start:
{
size_t v_i_boxed_1465_; size_t v_stop_boxed_1466_; lean_object* v_res_1467_; 
v_i_boxed_1465_ = lean_unbox_usize(v_i_1447_);
lean_dec(v_i_1447_);
v_stop_boxed_1466_ = lean_unbox_usize(v_stop_1448_);
lean_dec(v_stop_1448_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1446_, v_i_boxed_1465_, v_stop_boxed_1466_, v_b_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v_as_1446_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object* v_00_u03b1_1468_, lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_1469_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1486_ = _args[0];
lean_object* v_x_1487_ = _args[1];
lean_object* v___y_1488_ = _args[2];
lean_object* v___y_1489_ = _args[3];
lean_object* v___y_1490_ = _args[4];
lean_object* v___y_1491_ = _args[5];
lean_object* v___y_1492_ = _args[6];
lean_object* v___y_1493_ = _args[7];
lean_object* v___y_1494_ = _args[8];
lean_object* v___y_1495_ = _args[9];
lean_object* v___y_1496_ = _args[10];
lean_object* v___y_1497_ = _args[11];
lean_object* v___y_1498_ = _args[12];
lean_object* v___y_1499_ = _args[13];
lean_object* v___y_1500_ = _args[14];
lean_object* v___y_1501_ = _args[15];
lean_object* v___y_1502_ = _args[16];
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(v_00_u03b1_1486_, v_x_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object* v_oldTraces_1504_, lean_object* v_data_1505_, lean_object* v_ref_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_1504_, v_data_1505_, v_ref_1506_, v_msg_1507_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object** _args){
lean_object* v_oldTraces_1524_ = _args[0];
lean_object* v_data_1525_ = _args[1];
lean_object* v_ref_1526_ = _args[2];
lean_object* v_msg_1527_ = _args[3];
lean_object* v___y_1528_ = _args[4];
lean_object* v___y_1529_ = _args[5];
lean_object* v___y_1530_ = _args[6];
lean_object* v___y_1531_ = _args[7];
lean_object* v___y_1532_ = _args[8];
lean_object* v___y_1533_ = _args[9];
lean_object* v___y_1534_ = _args[10];
lean_object* v___y_1535_ = _args[11];
lean_object* v___y_1536_ = _args[12];
lean_object* v___y_1537_ = _args[13];
lean_object* v___y_1538_ = _args[14];
lean_object* v___y_1539_ = _args[15];
lean_object* v___y_1540_ = _args[16];
lean_object* v___y_1541_ = _args[17];
lean_object* v___y_1542_ = _args[18];
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1524_, v_data_1525_, v_ref_1526_, v_msg_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1543_;
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

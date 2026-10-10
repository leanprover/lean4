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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(lean_object* v_solved_24_){
_start:
{
lean_inc(v_solved_24_);
return v_solved_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg___boxed(lean_object* v_solved_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(v_solved_25_);
lean_dec(v_solved_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_solved_30_){
_start:
{
lean_inc(v_solved_30_);
return v_solved_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_solved_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(lean_box(0), v_t_28_, lean_box(0), v_solved_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_solved_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_solved_35_);
lean_dec(v_solved_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(lean_object* v_newHyps_38_){
_start:
{
lean_inc(v_newHyps_38_);
return v_newHyps_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg___boxed(lean_object* v_newHyps_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(v_newHyps_39_);
lean_dec(v_newHyps_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_newHyps_44_){
_start:
{
lean_inc(v_newHyps_44_);
return v_newHyps_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_newHyps_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(lean_box(0), v_t_42_, lean_box(0), v_newHyps_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_newHyps_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_newHyps_49_);
lean_dec(v_newHyps_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(lean_object* v_none_52_){
_start:
{
lean_inc(v_none_52_);
return v_none_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg___boxed(lean_object* v_none_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(v_none_53_);
lean_dec(v_none_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_none_58_){
_start:
{
lean_inc(v_none_58_);
return v_none_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_none_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(lean_box(0), v_t_56_, lean_box(0), v_none_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_none_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_none_63_);
lean_dec(v_none_63_);
return v_res_65_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(32u);
v___x_67_ = lean_mk_empty_array_with_capacity(v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_69_ = ((size_t)5ULL);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_unsigned_to_nat(32u);
v___x_72_ = lean_mk_empty_array_with_capacity(v___x_71_);
v___x_73_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0);
v___x_74_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_70_);
lean_ctor_set(v___x_74_, 3, v___x_70_);
lean_ctor_set_usize(v___x_74_, 4, v___x_69_);
return v___x_74_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; lean_object* v_traceState_78_; lean_object* v_traces_79_; lean_object* v___x_80_; lean_object* v_traceState_81_; lean_object* v_env_82_; lean_object* v_nextMacroScope_83_; lean_object* v_ngen_84_; lean_object* v_auxDeclNGen_85_; lean_object* v_cache_86_; lean_object* v_recordedDeps_87_; lean_object* v_messages_88_; lean_object* v_infoState_89_; lean_object* v_snapshotTasks_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_109_; 
v___x_77_ = lean_st_ref_get(v___y_75_);
v_traceState_78_ = lean_ctor_get(v___x_77_, 4);
lean_inc_ref(v_traceState_78_);
lean_dec(v___x_77_);
v_traces_79_ = lean_ctor_get(v_traceState_78_, 0);
lean_inc_ref(v_traces_79_);
lean_dec_ref(v_traceState_78_);
v___x_80_ = lean_st_ref_take(v___y_75_);
v_traceState_81_ = lean_ctor_get(v___x_80_, 4);
v_env_82_ = lean_ctor_get(v___x_80_, 0);
v_nextMacroScope_83_ = lean_ctor_get(v___x_80_, 1);
v_ngen_84_ = lean_ctor_get(v___x_80_, 2);
v_auxDeclNGen_85_ = lean_ctor_get(v___x_80_, 3);
v_cache_86_ = lean_ctor_get(v___x_80_, 5);
v_recordedDeps_87_ = lean_ctor_get(v___x_80_, 6);
v_messages_88_ = lean_ctor_get(v___x_80_, 7);
v_infoState_89_ = lean_ctor_get(v___x_80_, 8);
v_snapshotTasks_90_ = lean_ctor_get(v___x_80_, 9);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_109_ == 0)
{
v___x_92_ = v___x_80_;
v_isShared_93_ = v_isSharedCheck_109_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_snapshotTasks_90_);
lean_inc(v_infoState_89_);
lean_inc(v_messages_88_);
lean_inc(v_recordedDeps_87_);
lean_inc(v_cache_86_);
lean_inc(v_traceState_81_);
lean_inc(v_auxDeclNGen_85_);
lean_inc(v_ngen_84_);
lean_inc(v_nextMacroScope_83_);
lean_inc(v_env_82_);
lean_dec(v___x_80_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_109_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint64_t v_tid_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_107_; 
v_tid_94_ = lean_ctor_get_uint64(v_traceState_81_, sizeof(void*)*1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_traceState_81_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_traceState_81_, 0);
lean_dec(v_unused_108_);
v___x_96_ = v_traceState_81_;
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
else
{
lean_dec(v_traceState_81_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_98_);
lean_ctor_set_uint64(v_reuseFailAlloc_106_, sizeof(void*)*1, v_tid_94_);
v___x_100_ = v_reuseFailAlloc_106_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_100_);
v___x_102_ = v___x_92_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_env_82_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_nextMacroScope_83_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_ngen_84_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_auxDeclNGen_85_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_105_, 5, v_cache_86_);
lean_ctor_set(v_reuseFailAlloc_105_, 6, v_recordedDeps_87_);
lean_ctor_set(v_reuseFailAlloc_105_, 7, v_messages_88_);
lean_ctor_set(v_reuseFailAlloc_105_, 8, v_infoState_89_);
lean_ctor_set(v_reuseFailAlloc_105_, 9, v_snapshotTasks_90_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_st_ref_put(v___y_75_, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_traces_79_);
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_75_ = stack[0].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_75_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___boxed(lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_111_);
lean_dec(v___y_111_);
return v_res_113_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_127_);
return v___x_129_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_114_ = stack[0].m_obj;
lean_object* v___y_115_ = stack[1].m_obj;
lean_object* v___y_116_ = stack[2].m_obj;
lean_object* v___y_117_ = stack[3].m_obj;
lean_object* v___y_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v___y_120_ = stack[6].m_obj;
lean_object* v___y_121_ = stack[7].m_obj;
lean_object* v___y_122_ = stack[8].m_obj;
lean_object* v___y_123_ = stack[9].m_obj;
lean_object* v___y_124_ = stack[10].m_obj;
lean_object* v___y_125_ = stack[11].m_obj;
lean_object* v___y_126_ = stack[12].m_obj;
lean_object* v___y_127_ = stack[13].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_146_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
lean_object* v_name_149_; lean_object* v_defValue_150_; lean_object* v_map_151_; lean_object* v___x_152_; 
v_name_149_ = lean_ctor_get(v_opt_148_, 0);
v_defValue_150_ = lean_ctor_get(v_opt_148_, 1);
v_map_151_ = lean_ctor_get(v_opts_147_, 0);
v___x_152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_151_, v_name_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = lean_unbox(v_defValue_150_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; 
v_val_154_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_val_154_);
lean_dec_ref_known(v___x_152_, 1);
if (lean_obj_tag(v_val_154_) == 1)
{
uint8_t v_v_155_; 
v_v_155_ = lean_ctor_get_uint8(v_val_154_, 0);
lean_dec_ref_known(v_val_154_, 0);
return v_v_155_;
}
else
{
uint8_t v___x_156_; 
lean_dec(v_val_154_);
v___x_156_ = lean_unbox(v_defValue_150_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_147_ = stack[0].m_obj;
lean_object* v_opt_148_ = stack[1].m_obj;
uint8_t v_res_157_;
v_res_157_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_147_, v_opt_148_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object* v_opts_158_, lean_object* v_opt_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_158_, v_opt_159_);
lean_dec_ref(v_opt_159_);
lean_dec_ref(v_opts_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_165_ = stack[0].m_obj;
lean_object* v___y_166_ = stack[1].m_obj;
lean_object* v___y_167_ = stack[2].m_obj;
lean_object* v___y_168_ = stack[3].m_obj;
lean_object* v___y_169_ = stack[4].m_obj;
lean_object* v___y_170_ = stack[5].m_obj;
lean_object* v___y_171_ = stack[6].m_obj;
lean_object* v___y_172_ = stack[7].m_obj;
lean_object* v___y_173_ = stack[8].m_obj;
lean_object* v___y_174_ = stack[9].m_obj;
lean_object* v___y_175_ = stack[10].m_obj;
lean_object* v___y_176_ = stack[11].m_obj;
lean_object* v___y_177_ = stack[12].m_obj;
lean_object* v___y_178_ = stack[13].m_obj;
lean_object* v___y_179_ = stack[14].m_obj;
lean_object* v_res_183_;
v_res_183_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v_x_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object* v_x_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v_x_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec_ref(v_x_184_);
return v_res_200_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v_x_201_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v_x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v_x_201_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v_x_201_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 0);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_201_ = stack[0].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_201_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg___boxed(lean_object* v_x_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_220_);
return v_res_222_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(lean_object* v_e_223_){
_start:
{
if (lean_obj_tag(v_e_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 2;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 0;
return v___x_225_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_223_ = stack[0].m_obj;
uint8_t v_res_226_;
v_res_226_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_e_223_);
stack->m_num = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9___boxed(lean_object* v_e_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_e_227_);
lean_dec_ref(v_e_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(lean_object* v_opts_230_, lean_object* v_opt_231_){
_start:
{
lean_object* v_name_232_; lean_object* v_defValue_233_; lean_object* v_map_234_; lean_object* v___x_235_; 
v_name_232_ = lean_ctor_get(v_opt_231_, 0);
v_defValue_233_ = lean_ctor_get(v_opt_231_, 1);
v_map_234_ = lean_ctor_get(v_opts_230_, 0);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_234_, v_name_232_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_inc(v_defValue_233_);
return v_defValue_233_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_val_236_) == 3)
{
lean_object* v_v_237_; 
v_v_237_ = lean_ctor_get(v_val_236_, 0);
lean_inc(v_v_237_);
lean_dec_ref_known(v_val_236_, 1);
return v_v_237_;
}
else
{
lean_dec(v_val_236_);
lean_inc(v_defValue_233_);
return v_defValue_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10___boxed(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_238_, v_opt_239_);
lean_dec_ref(v_opt_239_);
lean_dec_ref(v_opts_238_);
return v_res_240_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(size_t v_sz_241_, size_t v_i_242_, lean_object* v_bs_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_lt(v_i_242_, v_sz_241_);
if (v___x_244_ == 0)
{
return v_bs_243_;
}
else
{
lean_object* v_v_245_; lean_object* v_msg_246_; lean_object* v___x_247_; lean_object* v_bs_x27_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; 
v_v_245_ = lean_array_uget_borrowed(v_bs_243_, v_i_242_);
v_msg_246_ = lean_ctor_get(v_v_245_, 1);
lean_inc_ref(v_msg_246_);
v___x_247_ = lean_unsigned_to_nat(0u);
v_bs_x27_248_ = lean_array_uset(v_bs_243_, v_i_242_, v___x_247_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_add(v_i_242_, v___x_249_);
v___x_251_ = lean_array_uset(v_bs_x27_248_, v_i_242_, v_msg_246_);
v_i_242_ = v___x_250_;
v_bs_243_ = v___x_251_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_241_ = stack[0].m_num;
size_t v_i_242_ = stack[1].m_num;
lean_object* v_bs_243_ = stack[2].m_obj;
lean_object* v_res_253_;
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_241_, v_i_242_, v_bs_243_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_bs_256_){
_start:
{
size_t v_sz_boxed_257_; size_t v_i_boxed_258_; lean_object* v_res_259_; 
v_sz_boxed_257_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_258_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_boxed_257_, v_i_boxed_258_, v_bs_256_);
return v_res_259_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; lean_object* v_env_267_; uint8_t v___x_268_; lean_object* v_env_269_; lean_object* v___x_270_; lean_object* v_toCold_271_; lean_object* v_mctx_272_; lean_object* v_lctx_273_; lean_object* v_options_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_266_ = lean_st_ref_get(v___y_264_);
v_env_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc_ref(v_env_267_);
lean_dec(v___x_266_);
v___x_268_ = 0;
v_env_269_ = l_Lean_Environment_setRecordingDeps(v_env_267_, v___x_268_);
v___x_270_ = lean_st_ref_get(v___y_262_);
v_toCold_271_ = lean_ctor_get(v___y_263_, 0);
v_mctx_272_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_mctx_272_);
lean_dec(v___x_270_);
v_lctx_273_ = lean_ctor_get(v___y_261_, 2);
v_options_274_ = lean_ctor_get(v_toCold_271_, 2);
lean_inc_ref(v_options_274_);
lean_inc_ref(v_lctx_273_);
v___x_275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_275_, 0, v_env_269_);
lean_ctor_set(v___x_275_, 1, v_mctx_272_);
lean_ctor_set(v___x_275_, 2, v_lctx_273_);
lean_ctor_set(v___x_275_, 3, v_options_274_);
v___x_276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_msgData_260_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_260_ = stack[0].m_obj;
lean_object* v___y_261_ = stack[1].m_obj;
lean_object* v___y_262_ = stack[2].m_obj;
lean_object* v___y_263_ = stack[3].m_obj;
lean_object* v___y_264_ = stack[4].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msgData_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msgData_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_285_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(lean_object* v_oldTraces_286_, lean_object* v_data_287_, lean_object* v_ref_288_, lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_toCold_295_; lean_object* v_currRecDepth_296_; lean_object* v_ref_297_; uint16_t v_optionFlags_298_; uint8_t v_suppressElabErrors_299_; uint8_t v_isRecordingDeps_300_; lean_object* v_ref_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_traceState_304_; lean_object* v_traces_305_; lean_object* v___x_306_; size_t v_sz_307_; size_t v___x_308_; lean_object* v___x_309_; lean_object* v_msg_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_350_; 
v_toCold_295_ = lean_ctor_get(v___y_292_, 0);
v_currRecDepth_296_ = lean_ctor_get(v___y_292_, 1);
v_ref_297_ = lean_ctor_get(v___y_292_, 2);
v_optionFlags_298_ = lean_ctor_get_uint16(v___y_292_, sizeof(void*)*3);
v_suppressElabErrors_299_ = lean_ctor_get_uint8(v___y_292_, sizeof(void*)*3 + 2);
v_isRecordingDeps_300_ = lean_ctor_get_uint8(v___y_292_, sizeof(void*)*3 + 3);
v_ref_301_ = l_Lean_replaceRef(v_ref_288_, v_ref_297_);
lean_inc(v_currRecDepth_296_);
lean_inc_ref(v_toCold_295_);
v___x_302_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_302_, 0, v_toCold_295_);
lean_ctor_set(v___x_302_, 1, v_currRecDepth_296_);
lean_ctor_set(v___x_302_, 2, v_ref_301_);
lean_ctor_set_uint16(v___x_302_, sizeof(void*)*3, v_optionFlags_298_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*3 + 2, v_suppressElabErrors_299_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*3 + 3, v_isRecordingDeps_300_);
v___x_303_ = lean_st_ref_get(v___y_293_);
v_traceState_304_ = lean_ctor_get(v___x_303_, 4);
lean_inc_ref(v_traceState_304_);
lean_dec(v___x_303_);
v_traces_305_ = lean_ctor_get(v_traceState_304_, 0);
lean_inc_ref(v_traces_305_);
lean_dec_ref(v_traceState_304_);
v___x_306_ = l_Lean_PersistentArray_toArray___redArg(v_traces_305_);
lean_dec_ref(v_traces_305_);
v_sz_307_ = lean_array_size(v___x_306_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_307_, v___x_308_, v___x_306_);
v_msg_310_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_310_, 0, v_data_287_);
lean_ctor_set(v_msg_310_, 1, v_msg_289_);
lean_ctor_set(v_msg_310_, 2, v___x_309_);
v___x_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_310_, v___y_290_, v___y_291_, v___x_302_, v___y_293_);
lean_dec_ref_known(v___x_302_, 3);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_350_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_350_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_350_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v_traceState_317_; lean_object* v_env_318_; lean_object* v_nextMacroScope_319_; lean_object* v_ngen_320_; lean_object* v_auxDeclNGen_321_; lean_object* v_cache_322_; lean_object* v_recordedDeps_323_; lean_object* v_messages_324_; lean_object* v_infoState_325_; lean_object* v_snapshotTasks_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_349_; 
v___x_316_ = lean_st_ref_take(v___y_293_);
v_traceState_317_ = lean_ctor_get(v___x_316_, 4);
v_env_318_ = lean_ctor_get(v___x_316_, 0);
v_nextMacroScope_319_ = lean_ctor_get(v___x_316_, 1);
v_ngen_320_ = lean_ctor_get(v___x_316_, 2);
v_auxDeclNGen_321_ = lean_ctor_get(v___x_316_, 3);
v_cache_322_ = lean_ctor_get(v___x_316_, 5);
v_recordedDeps_323_ = lean_ctor_get(v___x_316_, 6);
v_messages_324_ = lean_ctor_get(v___x_316_, 7);
v_infoState_325_ = lean_ctor_get(v___x_316_, 8);
v_snapshotTasks_326_ = lean_ctor_get(v___x_316_, 9);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_349_ == 0)
{
v___x_328_ = v___x_316_;
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snapshotTasks_326_);
lean_inc(v_infoState_325_);
lean_inc(v_messages_324_);
lean_inc(v_recordedDeps_323_);
lean_inc(v_cache_322_);
lean_inc(v_traceState_317_);
lean_inc(v_auxDeclNGen_321_);
lean_inc(v_ngen_320_);
lean_inc(v_nextMacroScope_319_);
lean_inc(v_env_318_);
lean_dec(v___x_316_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint64_t v_tid_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_347_; 
v_tid_330_ = lean_ctor_get_uint64(v_traceState_317_, sizeof(void*)*1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_traceState_317_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_traceState_317_, 0);
lean_dec(v_unused_348_);
v___x_332_ = v_traceState_317_;
v_isShared_333_ = v_isSharedCheck_347_;
goto v_resetjp_331_;
}
else
{
lean_dec(v_traceState_317_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_347_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_ref_288_);
lean_ctor_set(v___x_335_, 1, v_a_312_);
v___x_336_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_286_, v___x_335_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_336_);
v___x_338_ = v___x_332_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_336_);
lean_ctor_set_uint64(v_reuseFailAlloc_346_, sizeof(void*)*1, v_tid_330_);
v___x_338_ = v_reuseFailAlloc_346_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 4, v___x_338_);
v___x_340_ = v___x_328_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_env_318_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_nextMacroScope_319_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_ngen_320_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_auxDeclNGen_321_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 5, v_cache_322_);
lean_ctor_set(v_reuseFailAlloc_345_, 6, v_recordedDeps_323_);
lean_ctor_set(v_reuseFailAlloc_345_, 7, v_messages_324_);
lean_ctor_set(v_reuseFailAlloc_345_, 8, v_infoState_325_);
lean_ctor_set(v_reuseFailAlloc_345_, 9, v_snapshotTasks_326_);
v___x_340_ = v_reuseFailAlloc_345_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_st_ref_put(v___y_293_, v___x_340_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_334_);
v___x_343_ = v___x_314_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_334_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_286_ = stack[0].m_obj;
lean_object* v_data_287_ = stack[1].m_obj;
lean_object* v_ref_288_ = stack[2].m_obj;
lean_object* v_msg_289_ = stack[3].m_obj;
lean_object* v___y_290_ = stack[4].m_obj;
lean_object* v___y_291_ = stack[5].m_obj;
lean_object* v___y_292_ = stack[6].m_obj;
lean_object* v___y_293_ = stack[7].m_obj;
lean_object* v_res_351_;
v_res_351_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_286_, v_data_287_, v_ref_288_, v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_352_, lean_object* v_data_353_, lean_object* v_ref_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_352_, v_data_353_, v_ref_354_, v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0(void){
_start:
{
lean_object* v___x_362_; double v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_float_of_nat(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3(void){
_start:
{
lean_object* v___x_367_; double v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(1000u);
v___x_368_ = lean_float_of_nat(v___x_367_);
return v___x_368_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object* v_cls_369_, uint8_t v_collapsed_370_, lean_object* v_tag_371_, lean_object* v_opts_372_, uint8_t v_clsEnabled_373_, lean_object* v_oldTraces_374_, lean_object* v_msg_375_, lean_object* v_resStartStop_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v_data_397_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___y_413_; lean_object* v_a_414_; uint8_t v___y_429_; double v___y_461_; 
v_fst_392_ = lean_ctor_get(v_resStartStop_376_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v_resStartStop_376_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v_resStartStop_376_);
v_fst_408_ = lean_ctor_get(v_snd_393_, 0);
lean_inc(v_fst_408_);
v_snd_409_ = lean_ctor_get(v_snd_393_, 1);
lean_inc(v_snd_409_);
lean_dec(v_snd_393_);
v___x_410_ = l_Lean_trace_profiler;
v___x_411_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_372_, v___x_410_);
if (v___x_411_ == 0)
{
v___y_429_ = v___x_411_;
goto v___jp_428_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = l_Lean_trace_profiler_useHeartbeats;
v___x_467_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_372_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; double v___x_470_; double v___x_471_; double v___x_472_; 
v___x_468_ = l_Lean_trace_profiler_threshold;
v___x_469_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_372_, v___x_468_);
v___x_470_ = lean_float_of_nat(v___x_469_);
v___x_471_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3);
v___x_472_ = lean_float_div(v___x_470_, v___x_471_);
v___y_461_ = v___x_472_;
goto v___jp_460_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; double v___x_475_; 
v___x_473_ = l_Lean_trace_profiler_threshold;
v___x_474_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_372_, v___x_473_);
v___x_475_ = lean_float_of_nat(v___x_474_);
v___y_461_ = v___x_475_;
goto v___jp_460_;
}
}
v___jp_394_:
{
lean_object* v___x_398_; 
lean_inc(v___y_396_);
v___x_398_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_374_, v_data_397_, v___y_396_, v___y_395_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_392_);
return v___x_399_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_fst_392_);
v_a_400_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
v___jp_412_:
{
uint8_t v_result_415_; lean_object* v___x_416_; lean_object* v___x_417_; double v___x_418_; lean_object* v_data_419_; 
v_result_415_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_fst_392_);
v___x_416_ = lean_box(v_result_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0);
lean_inc_ref(v_tag_371_);
lean_inc_ref(v___x_417_);
lean_inc(v_cls_369_);
v_data_419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_419_, 0, v_cls_369_);
lean_ctor_set(v_data_419_, 1, v___x_417_);
lean_ctor_set(v_data_419_, 2, v_tag_371_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3, v___x_418_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3 + 8, v___x_418_);
lean_ctor_set_uint8(v_data_419_, sizeof(void*)*3 + 16, v_collapsed_370_);
if (v___x_411_ == 0)
{
lean_dec_ref_known(v___x_417_, 1);
lean_dec(v_snd_409_);
lean_dec(v_fst_408_);
lean_dec_ref(v_tag_371_);
lean_dec(v_cls_369_);
v___y_395_ = v_a_414_;
v___y_396_ = v___y_413_;
v_data_397_ = v_data_419_;
goto v___jp_394_;
}
else
{
lean_object* v_data_420_; double v___x_421_; double v___x_422_; 
lean_dec_ref_known(v_data_419_, 3);
v_data_420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_420_, 0, v_cls_369_);
lean_ctor_set(v_data_420_, 1, v___x_417_);
lean_ctor_set(v_data_420_, 2, v_tag_371_);
v___x_421_ = lean_unbox_float(v_fst_408_);
lean_dec(v_fst_408_);
lean_ctor_set_float(v_data_420_, sizeof(void*)*3, v___x_421_);
v___x_422_ = lean_unbox_float(v_snd_409_);
lean_dec(v_snd_409_);
lean_ctor_set_float(v_data_420_, sizeof(void*)*3 + 8, v___x_422_);
lean_ctor_set_uint8(v_data_420_, sizeof(void*)*3 + 16, v_collapsed_370_);
v___y_395_ = v_a_414_;
v___y_396_ = v___y_413_;
v_data_397_ = v_data_420_;
goto v___jp_394_;
}
}
v___jp_423_:
{
lean_object* v_ref_424_; lean_object* v___x_425_; 
v_ref_424_ = lean_ctor_get(v___y_389_, 2);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
lean_inc(v_fst_392_);
v___x_425_ = lean_apply_16(v_msg_375_, v_fst_392_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v___y_413_ = v_ref_424_;
v_a_414_ = v_a_426_;
goto v___jp_412_;
}
else
{
lean_object* v___x_427_; 
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2);
v___y_413_ = v_ref_424_;
v_a_414_ = v___x_427_;
goto v___jp_412_;
}
}
v___jp_428_:
{
if (v_clsEnabled_373_ == 0)
{
if (v___y_429_ == 0)
{
lean_object* v___x_430_; lean_object* v_traceState_431_; lean_object* v_env_432_; lean_object* v_nextMacroScope_433_; lean_object* v_ngen_434_; lean_object* v_auxDeclNGen_435_; lean_object* v_cache_436_; lean_object* v_recordedDeps_437_; lean_object* v_messages_438_; lean_object* v_infoState_439_; lean_object* v_snapshotTasks_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_snd_409_);
lean_dec(v_fst_408_);
lean_dec_ref(v_msg_375_);
lean_dec_ref(v_tag_371_);
lean_dec(v_cls_369_);
v___x_430_ = lean_st_ref_take(v___y_390_);
v_traceState_431_ = lean_ctor_get(v___x_430_, 4);
v_env_432_ = lean_ctor_get(v___x_430_, 0);
v_nextMacroScope_433_ = lean_ctor_get(v___x_430_, 1);
v_ngen_434_ = lean_ctor_get(v___x_430_, 2);
v_auxDeclNGen_435_ = lean_ctor_get(v___x_430_, 3);
v_cache_436_ = lean_ctor_get(v___x_430_, 5);
v_recordedDeps_437_ = lean_ctor_get(v___x_430_, 6);
v_messages_438_ = lean_ctor_get(v___x_430_, 7);
v_infoState_439_ = lean_ctor_get(v___x_430_, 8);
v_snapshotTasks_440_ = lean_ctor_get(v___x_430_, 9);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_459_ == 0)
{
v___x_442_ = v___x_430_;
v_isShared_443_ = v_isSharedCheck_459_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snapshotTasks_440_);
lean_inc(v_infoState_439_);
lean_inc(v_messages_438_);
lean_inc(v_recordedDeps_437_);
lean_inc(v_cache_436_);
lean_inc(v_traceState_431_);
lean_inc(v_auxDeclNGen_435_);
lean_inc(v_ngen_434_);
lean_inc(v_nextMacroScope_433_);
lean_inc(v_env_432_);
lean_dec(v___x_430_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_459_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint64_t v_tid_444_; lean_object* v_traces_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_458_; 
v_tid_444_ = lean_ctor_get_uint64(v_traceState_431_, sizeof(void*)*1);
v_traces_445_ = lean_ctor_get(v_traceState_431_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_traceState_431_);
if (v_isSharedCheck_458_ == 0)
{
v___x_447_ = v_traceState_431_;
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_traces_445_);
lean_dec(v_traceState_431_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_374_, v_traces_445_);
lean_dec_ref(v_traces_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_449_);
lean_ctor_set_uint64(v_reuseFailAlloc_457_, sizeof(void*)*1, v_tid_444_);
v___x_451_ = v_reuseFailAlloc_457_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 4, v___x_451_);
v___x_453_ = v___x_442_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_env_432_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_nextMacroScope_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_ngen_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_auxDeclNGen_435_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_cache_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_recordedDeps_437_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_messages_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_infoState_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 9, v_snapshotTasks_440_);
v___x_453_ = v_reuseFailAlloc_456_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_st_ref_put(v___y_390_, v___x_453_);
v___x_455_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_392_);
return v___x_455_;
}
}
}
}
}
else
{
goto v___jp_423_;
}
}
else
{
goto v___jp_423_;
}
}
v___jp_460_:
{
double v___x_462_; double v___x_463_; double v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unbox_float(v_snd_409_);
v___x_463_ = lean_unbox_float(v_fst_408_);
v___x_464_ = lean_float_sub(v___x_462_, v___x_463_);
v___x_465_ = lean_float_decLt(v___y_461_, v___x_464_);
v___y_429_ = v___x_465_;
goto v___jp_428_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_369_ = stack[0].m_obj;
uint8_t v_collapsed_370_ = stack[1].m_num;
lean_object* v_tag_371_ = stack[2].m_obj;
lean_object* v_opts_372_ = stack[3].m_obj;
uint8_t v_clsEnabled_373_ = stack[4].m_num;
lean_object* v_oldTraces_374_ = stack[5].m_obj;
lean_object* v_msg_375_ = stack[6].m_obj;
lean_object* v_resStartStop_376_ = stack[7].m_obj;
lean_object* v___y_377_ = stack[8].m_obj;
lean_object* v___y_378_ = stack[9].m_obj;
lean_object* v___y_379_ = stack[10].m_obj;
lean_object* v___y_380_ = stack[11].m_obj;
lean_object* v___y_381_ = stack[12].m_obj;
lean_object* v___y_382_ = stack[13].m_obj;
lean_object* v___y_383_ = stack[14].m_obj;
lean_object* v___y_384_ = stack[15].m_obj;
lean_object* v___y_385_ = stack[16].m_obj;
lean_object* v___y_386_ = stack[17].m_obj;
lean_object* v___y_387_ = stack[18].m_obj;
lean_object* v___y_388_ = stack[19].m_obj;
lean_object* v___y_389_ = stack[20].m_obj;
lean_object* v___y_390_ = stack[21].m_obj;
lean_object* v_res_476_;
v_res_476_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_cls_369_, v_collapsed_370_, v_tag_371_, v_opts_372_, v_clsEnabled_373_, v_oldTraces_374_, v_msg_375_, v_resStartStop_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object** _args){
lean_object* v_cls_477_ = _args[0];
lean_object* v_collapsed_478_ = _args[1];
lean_object* v_tag_479_ = _args[2];
lean_object* v_opts_480_ = _args[3];
lean_object* v_clsEnabled_481_ = _args[4];
lean_object* v_oldTraces_482_ = _args[5];
lean_object* v_msg_483_ = _args[6];
lean_object* v_resStartStop_484_ = _args[7];
lean_object* v___y_485_ = _args[8];
lean_object* v___y_486_ = _args[9];
lean_object* v___y_487_ = _args[10];
lean_object* v___y_488_ = _args[11];
lean_object* v___y_489_ = _args[12];
lean_object* v___y_490_ = _args[13];
lean_object* v___y_491_ = _args[14];
lean_object* v___y_492_ = _args[15];
lean_object* v___y_493_ = _args[16];
lean_object* v___y_494_ = _args[17];
lean_object* v___y_495_ = _args[18];
lean_object* v___y_496_ = _args[19];
lean_object* v___y_497_ = _args[20];
lean_object* v___y_498_ = _args[21];
lean_object* v___y_499_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_500_; uint8_t v_clsEnabled_boxed_501_; lean_object* v_res_502_; 
v_collapsed_boxed_500_ = lean_unbox(v_collapsed_478_);
v_clsEnabled_boxed_501_ = lean_unbox(v_clsEnabled_481_);
v_res_502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_cls_477_, v_collapsed_boxed_500_, v_tag_479_, v_opts_480_, v_clsEnabled_boxed_501_, v_oldTraces_482_, v_msg_483_, v_resStartStop_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v_opts_480_);
return v_res_502_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(size_t v_sz_503_, size_t v_i_504_, lean_object* v_bs_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_504_, v_sz_503_);
if (v___x_506_ == 0)
{
return v_bs_505_;
}
else
{
lean_object* v_v_507_; lean_object* v_hyp_508_; lean_object* v___x_509_; lean_object* v_bs_x27_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_v_507_ = lean_array_uget_borrowed(v_bs_505_, v_i_504_);
v_hyp_508_ = lean_ctor_get(v_v_507_, 0);
lean_inc_ref(v_hyp_508_);
v___x_509_ = lean_unsigned_to_nat(0u);
v_bs_x27_510_ = lean_array_uset(v_bs_505_, v_i_504_, v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_504_, v___x_511_);
v___x_513_ = lean_array_uset(v_bs_x27_510_, v_i_504_, v_hyp_508_);
v_i_504_ = v___x_512_;
v_bs_505_ = v___x_513_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_503_ = stack[0].m_num;
size_t v_i_504_ = stack[1].m_num;
lean_object* v_bs_505_ = stack[2].m_obj;
lean_object* v_res_515_;
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_503_, v_i_504_, v_bs_505_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
return v_res_521_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_ref_528_; lean_object* v___x_529_; lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
v_ref_528_ = lean_ctor_get(v___y_525_, 2);
v___x_529_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_538_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_inc(v_ref_528_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_ref_528_);
lean_ctor_set(v___x_534_, 1, v_a_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 1);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_522_ = stack[0].m_obj;
lean_object* v___y_523_ = stack[1].m_obj;
lean_object* v___y_524_ = stack[2].m_obj;
lean_object* v___y_525_ = stack[3].m_obj;
lean_object* v___y_526_ = stack[4].m_obj;
lean_object* v_res_539_;
v_res_539_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3));
v___x_553_ = l_Lean_stringToMessageData(v___x_552_);
return v___x_553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object* v_as_554_, size_t v_sz_555_, size_t v_i_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_a_574_; uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v_b_557_);
return v___x_579_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_580_ = lean_array_uget_borrowed(v_as_554_, v_i_556_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0));
v___x_582_ = l_Lean_Core_checkSystem(v___x_581_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_type_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
lean_dec_ref_known(v___x_582_, 1);
v_type_583_ = lean_ctor_get(v_a_580_, 1);
v___x_584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2));
v___x_585_ = l_Lean_Expr_isConstOf(v_type_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v___y_560_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref_known(v___x_586_, 1);
lean_inc(v_a_580_);
v___x_587_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_a_580_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
if (lean_obj_tag(v_a_588_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_590_; 
v_val_589_ = lean_ctor_get(v_a_588_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_a_588_, 1);
v___x_590_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v___y_560_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Array_append___redArg(v_b_557_, v_a_591_);
lean_dec(v_a_591_);
v___x_593_ = lean_array_push(v___x_592_, v_val_589_);
v_a_574_ = v___x_593_;
goto v___jp_573_;
}
else
{
lean_dec(v_val_589_);
lean_dec_ref(v_b_557_);
return v___x_590_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_a_588_);
v___x_594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4);
lean_inc_ref(v_type_583_);
v___x_595_ = l_Lean_MessageData_ofExpr(v_type_583_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v___x_596_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_dec_ref_known(v___x_597_, 1);
v_a_574_ = v_b_557_;
goto v___jp_573_;
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_b_557_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
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
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_b_557_);
v_a_606_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_587_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_587_);
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
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_b_557_);
v_a_614_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_586_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_586_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
v_a_574_ = v_b_557_;
goto v___jp_573_;
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_b_557_);
v_a_622_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_582_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_582_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
v___jp_573_:
{
size_t v___x_575_; size_t v___x_576_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_556_, v___x_575_);
v_i_556_ = v___x_576_;
v_b_557_ = v_a_574_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_554_ = stack[0].m_obj;
size_t v_sz_555_ = stack[1].m_num;
size_t v_i_556_ = stack[2].m_num;
lean_object* v_b_557_ = stack[3].m_obj;
lean_object* v___y_558_ = stack[4].m_obj;
lean_object* v___y_559_ = stack[5].m_obj;
lean_object* v___y_560_ = stack[6].m_obj;
lean_object* v___y_561_ = stack[7].m_obj;
lean_object* v___y_562_ = stack[8].m_obj;
lean_object* v___y_563_ = stack[9].m_obj;
lean_object* v___y_564_ = stack[10].m_obj;
lean_object* v___y_565_ = stack[11].m_obj;
lean_object* v___y_566_ = stack[12].m_obj;
lean_object* v___y_567_ = stack[13].m_obj;
lean_object* v___y_568_ = stack[14].m_obj;
lean_object* v___y_569_ = stack[15].m_obj;
lean_object* v___y_570_ = stack[16].m_obj;
lean_object* v___y_571_ = stack[17].m_obj;
lean_object* v_res_630_;
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_554_, v_sz_555_, v_i_556_, v_b_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object** _args){
lean_object* v_as_631_ = _args[0];
lean_object* v_sz_632_ = _args[1];
lean_object* v_i_633_ = _args[2];
lean_object* v_b_634_ = _args[3];
lean_object* v___y_635_ = _args[4];
lean_object* v___y_636_ = _args[5];
lean_object* v___y_637_ = _args[6];
lean_object* v___y_638_ = _args[7];
lean_object* v___y_639_ = _args[8];
lean_object* v___y_640_ = _args[9];
lean_object* v___y_641_ = _args[10];
lean_object* v___y_642_ = _args[11];
lean_object* v___y_643_ = _args[12];
lean_object* v___y_644_ = _args[13];
lean_object* v___y_645_ = _args[14];
lean_object* v___y_646_ = _args[15];
lean_object* v___y_647_ = _args[16];
lean_object* v___y_648_ = _args[17];
lean_object* v___y_649_ = _args[18];
_start:
{
size_t v_sz_boxed_650_; size_t v_i_boxed_651_; lean_object* v_res_652_; 
v_sz_boxed_650_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_651_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_631_, v_sz_boxed_650_, v_i_boxed_651_, v_b_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_as_631_);
return v_res_652_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(lean_object* v_as_653_, size_t v_i_654_, size_t v_stop_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_eq(v_i_654_, v_stop_655_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_array_uget_borrowed(v_as_653_, v_i_654_);
lean_inc(v___x_665_);
v___x_666_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_656_, v___x_665_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; size_t v___x_668_; size_t v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_654_, v___x_668_);
v_i_654_ = v___x_669_;
v_b_656_ = v_a_667_;
goto _start;
}
else
{
return v___x_666_;
}
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_b_656_);
return v___x_671_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_653_ = stack[0].m_obj;
size_t v_i_654_ = stack[1].m_num;
size_t v_stop_655_ = stack[2].m_num;
lean_object* v_b_656_ = stack[3].m_obj;
lean_object* v___y_657_ = stack[4].m_obj;
lean_object* v___y_658_ = stack[5].m_obj;
lean_object* v___y_659_ = stack[6].m_obj;
lean_object* v___y_660_ = stack[7].m_obj;
lean_object* v___y_661_ = stack[8].m_obj;
lean_object* v___y_662_ = stack[9].m_obj;
lean_object* v_res_672_;
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_653_, v_i_654_, v_stop_655_, v_b_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
stack->m_obj
 = v_res_672_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg___boxed(lean_object* v_as_673_, lean_object* v_i_674_, lean_object* v_stop_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_i_boxed_684_; size_t v_stop_boxed_685_; lean_object* v_res_686_; 
v_i_boxed_684_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_stop_boxed_685_ = lean_unbox_usize(v_stop_675_);
lean_dec(v_stop_675_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_673_, v_i_boxed_684_, v_stop_boxed_685_, v_b_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_as_673_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2);
v___x_694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
lean_ctor_set(v___x_694_, 3, v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_unsigned_to_nat(16u);
v___x_697_ = lean_mk_array(v___x_696_, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
v___x_702_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_720_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16));
v___x_721_ = l_Lean_Name_append(v___x_720_, v___x_719_);
return v___x_721_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18(void){
_start:
{
lean_object* v___x_722_; double v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(1000000000u);
v___x_723_ = lean_float_of_nat(v___x_722_);
return v___x_723_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___y_740_; lean_object* v_a_741_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v_hypQueue_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v_toCold_951_; lean_object* v_options_952_; uint8_t v_hasTrace_953_; 
v_toCold_951_ = lean_ctor_get(v_a_736_, 0);
v_options_952_ = lean_ctor_get(v_toCold_951_, 2);
v_hasTrace_953_ = lean_ctor_get_uint8(v_options_952_, sizeof(void*)*1);
if (v_hasTrace_953_ == 0)
{
lean_object* v___x_954_; lean_object* v_satExpr_955_; lean_object* v_hypQueue_956_; lean_object* v_usedHyps_957_; uint8_t v_didChange_958_; lean_object* v_theoryState_959_; lean_object* v_solverTimeBudgetMs_960_; lean_object* v_roundBudget_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_971_; 
v___x_954_ = lean_st_ref_take(v_a_725_);
v_satExpr_955_ = lean_ctor_get(v___x_954_, 0);
v_hypQueue_956_ = lean_ctor_get(v___x_954_, 1);
v_usedHyps_957_ = lean_ctor_get(v___x_954_, 2);
v_didChange_958_ = lean_ctor_get_uint8(v___x_954_, sizeof(void*)*6);
v_theoryState_959_ = lean_ctor_get(v___x_954_, 3);
v_solverTimeBudgetMs_960_ = lean_ctor_get(v___x_954_, 4);
v_roundBudget_961_ = lean_ctor_get(v___x_954_, 5);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_971_ == 0)
{
v___x_963_ = v___x_954_;
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_roundBudget_961_);
lean_inc(v_solverTimeBudgetMs_960_);
lean_inc(v_theoryState_959_);
lean_inc(v_usedHyps_957_);
lean_inc(v_hypQueue_956_);
lean_inc(v_satExpr_955_);
lean_dec(v___x_954_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_966_ = l_Array_append___redArg(v_usedHyps_957_, v_hypQueue_956_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v___x_966_);
lean_ctor_set(v___x_963_, 1, v___x_965_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_satExpr_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_theoryState_959_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_solverTimeBudgetMs_960_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v_roundBudget_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*6, v_didChange_958_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_st_ref_put(v_a_725_, v___x_968_);
v_hypQueue_774_ = v_hypQueue_956_;
v___y_775_ = v_a_724_;
v___y_776_ = v_a_725_;
v___y_777_ = v_a_726_;
v___y_778_ = v_a_727_;
v___y_779_ = v_a_728_;
v___y_780_ = v_a_729_;
v___y_781_ = v_a_730_;
v___y_782_ = v_a_731_;
v___y_783_ = v_a_732_;
v___y_784_ = v_a_733_;
v___y_785_ = v_a_734_;
v___y_786_ = v_a_735_;
v___y_787_ = v_a_736_;
v___y_788_ = v_a_737_;
goto v___jp_773_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v_a_981_; lean_object* v___y_994_; lean_object* v___y_995_; uint8_t v_a_996_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v_a_1002_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v_a_1023_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v_a_1034_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v_a_1046_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v_a_1052_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v_a_1073_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; 
v_inheritedTraceOptions_972_ = lean_ctor_get(v_toCold_951_, 11);
v___f_973_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_974_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_975_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_976_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_972_, v_options_952_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_trace_profiler;
v___x_1393_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_952_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v_satExpr_1395_; lean_object* v_hypQueue_1396_; lean_object* v_usedHyps_1397_; uint8_t v_didChange_1398_; lean_object* v_theoryState_1399_; lean_object* v_solverTimeBudgetMs_1400_; lean_object* v_roundBudget_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v___x_1394_ = lean_st_ref_take(v_a_725_);
v_satExpr_1395_ = lean_ctor_get(v___x_1394_, 0);
v_hypQueue_1396_ = lean_ctor_get(v___x_1394_, 1);
v_usedHyps_1397_ = lean_ctor_get(v___x_1394_, 2);
v_didChange_1398_ = lean_ctor_get_uint8(v___x_1394_, sizeof(void*)*6);
v_theoryState_1399_ = lean_ctor_get(v___x_1394_, 3);
v_solverTimeBudgetMs_1400_ = lean_ctor_get(v___x_1394_, 4);
v_roundBudget_1401_ = lean_ctor_get(v___x_1394_, 5);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v___x_1394_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_roundBudget_1401_);
lean_inc(v_solverTimeBudgetMs_1400_);
lean_inc(v_theoryState_1399_);
lean_inc(v_usedHyps_1397_);
lean_inc(v_hypQueue_1396_);
lean_inc(v_satExpr_1395_);
lean_dec(v___x_1394_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1406_ = l_Array_append___redArg(v_usedHyps_1397_, v_hypQueue_1396_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 2, v___x_1406_);
lean_ctor_set(v___x_1403_, 1, v___x_1405_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_satExpr_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_theoryState_1399_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_solverTimeBudgetMs_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_roundBudget_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*6, v_didChange_1398_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_st_ref_put(v_a_725_, v___x_1408_);
v_hypQueue_774_ = v_hypQueue_1396_;
v___y_775_ = v_a_724_;
v___y_776_ = v_a_725_;
v___y_777_ = v_a_726_;
v___y_778_ = v_a_727_;
v___y_779_ = v_a_728_;
v___y_780_ = v_a_729_;
v___y_781_ = v_a_730_;
v___y_782_ = v_a_731_;
v___y_783_ = v_a_732_;
v___y_784_ = v_a_733_;
v___y_785_ = v_a_734_;
v___y_786_ = v_a_735_;
v___y_787_ = v_a_736_;
v___y_788_ = v_a_737_;
goto v___jp_773_;
}
}
}
else
{
goto v___jp_1081_;
}
}
else
{
goto v___jp_1081_;
}
v___jp_978_:
{
lean_object* v___x_982_; double v___x_983_; double v___x_984_; double v___x_985_; double v___x_986_; double v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_982_ = lean_io_mono_nanos_now();
v___x_983_ = lean_float_of_nat(v___y_980_);
v___x_984_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
v___x_985_ = lean_float_div(v___x_983_, v___x_984_);
v___x_986_ = lean_float_of_nat(v___x_982_);
v___x_987_ = lean_float_div(v___x_986_, v___x_984_);
v___x_988_ = lean_box_float(v___x_985_);
v___x_989_ = lean_box_float(v___x_987_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_981_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_974_, v_hasTrace_953_, v___x_975_, v_options_952_, v___x_977_, v___y_979_, v___f_973_, v___x_991_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_992_;
}
v___jp_993_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_box(v_a_996_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___y_979_ = v___y_994_;
v___y_980_ = v___y_995_;
v_a_981_ = v___x_998_;
goto v___jp_978_;
}
v___jp_999_:
{
lean_object* v___x_1003_; lean_object* v_hypQueue_1004_; lean_object* v_usedHyps_1005_; uint8_t v_didChange_1006_; lean_object* v_theoryState_1007_; lean_object* v_solverTimeBudgetMs_1008_; lean_object* v_roundBudget_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1018_; 
v___x_1003_ = lean_st_ref_take(v_a_725_);
v_hypQueue_1004_ = lean_ctor_get(v___x_1003_, 1);
v_usedHyps_1005_ = lean_ctor_get(v___x_1003_, 2);
v_didChange_1006_ = lean_ctor_get_uint8(v___x_1003_, sizeof(void*)*6);
v_theoryState_1007_ = lean_ctor_get(v___x_1003_, 3);
v_solverTimeBudgetMs_1008_ = lean_ctor_get(v___x_1003_, 4);
v_roundBudget_1009_ = lean_ctor_get(v___x_1003_, 5);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_1003_, 0);
lean_dec(v_unused_1019_);
v___x_1011_ = v___x_1003_;
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_roundBudget_1009_);
lean_inc(v_solverTimeBudgetMs_1008_);
lean_inc(v_theoryState_1007_);
lean_inc(v_usedHyps_1005_);
lean_inc(v_hypQueue_1004_);
lean_dec(v___x_1003_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_a_1002_);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_hypQueue_1004_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_usedHyps_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_theoryState_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_solverTimeBudgetMs_1008_);
lean_ctor_set(v_reuseFailAlloc_1017_, 5, v_roundBudget_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1017_, sizeof(void*)*6, v_didChange_1006_);
v___x_1014_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_st_ref_put(v_a_725_, v___x_1014_);
v___x_1016_ = 1;
v___y_994_ = v___y_1000_;
v___y_995_ = v___y_1001_;
v_a_996_ = v___x_1016_;
goto v___jp_993_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1023_);
v___y_979_ = v___y_1021_;
v___y_980_ = v___y_1022_;
v_a_981_ = v___x_1024_;
goto v___jp_978_;
}
v___jp_1025_:
{
if (lean_obj_tag(v___y_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___y_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___y_1028_, 1);
v___y_1000_ = v___y_1026_;
v___y_1001_ = v___y_1027_;
v_a_1002_ = v_a_1029_;
goto v___jp_999_;
}
else
{
lean_object* v_a_1030_; 
v_a_1030_ = lean_ctor_get(v___y_1028_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___y_1028_, 1);
v___y_1021_ = v___y_1026_;
v___y_1022_ = v___y_1027_;
v_a_1023_ = v_a_1030_;
goto v___jp_1020_;
}
}
v___jp_1031_:
{
lean_object* v___x_1035_; double v___x_1036_; double v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1035_ = lean_io_get_num_heartbeats();
v___x_1036_ = lean_float_of_nat(v___y_1033_);
v___x_1037_ = lean_float_of_nat(v___x_1035_);
v___x_1038_ = lean_box_float(v___x_1036_);
v___x_1039_ = lean_box_float(v___x_1037_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1034_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_974_, v_hasTrace_953_, v___x_975_, v_options_952_, v___x_977_, v___y_1032_, v___f_973_, v___x_1041_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_1042_;
}
v___jp_1043_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_box(v_a_1046_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___y_1032_ = v___y_1044_;
v___y_1033_ = v___y_1045_;
v_a_1034_ = v___x_1048_;
goto v___jp_1031_;
}
v___jp_1049_:
{
lean_object* v___x_1053_; lean_object* v_hypQueue_1054_; lean_object* v_usedHyps_1055_; uint8_t v_didChange_1056_; lean_object* v_theoryState_1057_; lean_object* v_solverTimeBudgetMs_1058_; lean_object* v_roundBudget_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
v___x_1053_ = lean_st_ref_take(v_a_725_);
v_hypQueue_1054_ = lean_ctor_get(v___x_1053_, 1);
v_usedHyps_1055_ = lean_ctor_get(v___x_1053_, 2);
v_didChange_1056_ = lean_ctor_get_uint8(v___x_1053_, sizeof(void*)*6);
v_theoryState_1057_ = lean_ctor_get(v___x_1053_, 3);
v_solverTimeBudgetMs_1058_ = lean_ctor_get(v___x_1053_, 4);
v_roundBudget_1059_ = lean_ctor_get(v___x_1053_, 5);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1069_);
v___x_1061_ = v___x_1053_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_roundBudget_1059_);
lean_inc(v_solverTimeBudgetMs_1058_);
lean_inc(v_theoryState_1057_);
lean_inc(v_usedHyps_1055_);
lean_inc(v_hypQueue_1054_);
lean_dec(v___x_1053_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_a_1052_);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_hypQueue_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_usedHyps_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_theoryState_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_solverTimeBudgetMs_1058_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_roundBudget_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1067_, sizeof(void*)*6, v_didChange_1056_);
v___x_1064_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_st_ref_put(v_a_725_, v___x_1064_);
v___x_1066_ = 1;
v___y_1044_ = v___y_1050_;
v___y_1045_ = v___y_1051_;
v_a_1046_ = v___x_1066_;
goto v___jp_1043_;
}
}
}
v___jp_1070_:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1073_);
v___y_1032_ = v___y_1071_;
v___y_1033_ = v___y_1072_;
v_a_1034_ = v___x_1074_;
goto v___jp_1031_;
}
v___jp_1075_:
{
if (lean_obj_tag(v___y_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___y_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___y_1078_, 1);
v___y_1050_ = v___y_1076_;
v___y_1051_ = v___y_1077_;
v_a_1052_ = v_a_1079_;
goto v___jp_1049_;
}
else
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___y_1078_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___y_1078_, 1);
v___y_1071_ = v___y_1076_;
v___y_1072_ = v___y_1077_;
v_a_1073_ = v_a_1080_;
goto v___jp_1070_;
}
}
v___jp_1081_:
{
lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1391_; 
v___x_1082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v_a_737_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1391_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1391_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1088_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_952_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_satExpr_1091_; lean_object* v_hypQueue_1092_; lean_object* v_usedHyps_1093_; uint8_t v_didChange_1094_; lean_object* v_theoryState_1095_; lean_object* v_solverTimeBudgetMs_1096_; lean_object* v_roundBudget_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1239_; 
v___x_1089_ = lean_io_mono_nanos_now();
v___x_1090_ = lean_st_ref_take(v_a_725_);
v_satExpr_1091_ = lean_ctor_get(v___x_1090_, 0);
v_hypQueue_1092_ = lean_ctor_get(v___x_1090_, 1);
v_usedHyps_1093_ = lean_ctor_get(v___x_1090_, 2);
v_didChange_1094_ = lean_ctor_get_uint8(v___x_1090_, sizeof(void*)*6);
v_theoryState_1095_ = lean_ctor_get(v___x_1090_, 3);
v_solverTimeBudgetMs_1096_ = lean_ctor_get(v___x_1090_, 4);
v_roundBudget_1097_ = lean_ctor_get(v___x_1090_, 5);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1099_ = v___x_1090_;
v_isShared_1100_ = v_isSharedCheck_1239_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_roundBudget_1097_);
lean_inc(v_solverTimeBudgetMs_1096_);
lean_inc(v_theoryState_1095_);
lean_inc(v_usedHyps_1093_);
lean_inc(v_hypQueue_1092_);
lean_inc(v_satExpr_1091_);
lean_dec(v___x_1090_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1239_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1103_ = l_Array_append___redArg(v_usedHyps_1093_, v_hypQueue_1092_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 2, v___x_1103_);
lean_ctor_set(v___x_1099_, 1, v___x_1102_);
v___x_1105_ = v___x_1099_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_satExpr_1091_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_theoryState_1095_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_solverTimeBudgetMs_1096_);
lean_ctor_set(v_reuseFailAlloc_1238_, 5, v_roundBudget_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*6, v_didChange_1094_);
v___x_1105_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_st_ref_put(v_a_725_, v___x_1105_);
v___x_1107_ = lean_array_get_size(v_hypQueue_1092_);
v___x_1108_ = lean_nat_dec_eq(v___x_1107_, v___x_1101_);
if (v___x_1108_ == 0)
{
lean_object* v_goal_1109_; lean_object* v_tacticContext_1110_; lean_object* v___x_1111_; lean_object* v_config_1112_; lean_object* v_mode_1113_; lean_object* v_timeout_1114_; uint8_t v_trimProofs_1115_; uint8_t v_binaryProofs_1116_; uint8_t v_acNf_1117_; uint8_t v_andFlattening_1118_; uint8_t v_embeddedConstraintSubst_1119_; uint8_t v_graphviz_1120_; lean_object* v_maxSteps_1121_; uint8_t v_solverMode_1122_; uint8_t v_uf_1123_; lean_object* v_cegarRounds_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1236_; 
v_goal_1109_ = lean_ctor_get(v_a_724_, 0);
v_tacticContext_1110_ = lean_ctor_get(v_a_724_, 2);
lean_inc_ref(v_tacticContext_1110_);
v___x_1111_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1110_);
v_config_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_config_1112_);
v_mode_1113_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_mode_1113_);
lean_dec_ref(v___x_1111_);
v_timeout_1114_ = lean_ctor_get(v_config_1112_, 0);
v_trimProofs_1115_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3);
v_binaryProofs_1116_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 1);
v_acNf_1117_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 2);
v_andFlattening_1118_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1119_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 4);
v_graphviz_1120_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 8);
v_maxSteps_1121_ = lean_ctor_get(v_config_1112_, 1);
v_solverMode_1122_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 10);
v_uf_1123_ = lean_ctor_get_uint8(v_config_1112_, sizeof(void*)*3 + 11);
v_cegarRounds_1124_ = lean_ctor_get(v_config_1112_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_config_1112_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1126_ = v_config_1112_;
v_isShared_1127_ = v_isSharedCheck_1236_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_cegarRounds_1124_);
lean_inc(v_maxSteps_1121_);
lean_inc(v_timeout_1114_);
lean_dec(v_config_1112_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1236_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
lean_inc(v_goal_1109_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_goal_1109_);
v___x_1129_ = v___x_1085_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_goal_1109_);
v___x_1129_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1127_ == 0)
{
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_timeout_1114_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_maxSteps_1121_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_cegarRounds_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3, v_trimProofs_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 1, v_binaryProofs_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 2, v_acNf_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 3, v_andFlattening_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 8, v_graphviz_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 10, v_solverMode_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 11, v_uf_1123_);
v___x_1131_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_theoryState_1136_; lean_object* v_satExpr_1137_; lean_object* v_hypQueue_1138_; lean_object* v_usedHyps_1139_; uint8_t v_didChange_1140_; lean_object* v_solverTimeBudgetMs_1141_; lean_object* v_roundBudget_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1233_; 
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*3 + 5, v___x_1108_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*3 + 6, v___x_1108_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*3 + 7, v___x_1108_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*3 + 9, v___x_1108_);
v___x_1132_ = lean_box(v_hasTrace_953_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1113_, v___x_1131_, v___x_1133_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = lean_st_ref_take(v_a_725_);
v_theoryState_1136_ = lean_ctor_get(v___x_1135_, 3);
v_satExpr_1137_ = lean_ctor_get(v___x_1135_, 0);
v_hypQueue_1138_ = lean_ctor_get(v___x_1135_, 1);
v_usedHyps_1139_ = lean_ctor_get(v___x_1135_, 2);
v_didChange_1140_ = lean_ctor_get_uint8(v___x_1135_, sizeof(void*)*6);
v_solverTimeBudgetMs_1141_ = lean_ctor_get(v___x_1135_, 4);
v_roundBudget_1142_ = lean_ctor_get(v___x_1135_, 5);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1144_ = v___x_1135_;
v_isShared_1145_ = v_isSharedCheck_1233_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_roundBudget_1142_);
lean_inc(v_solverTimeBudgetMs_1141_);
lean_inc(v_theoryState_1136_);
lean_inc(v_usedHyps_1139_);
lean_inc(v_hypQueue_1138_);
lean_inc(v_satExpr_1137_);
lean_dec(v___x_1135_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1233_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_funState_1146_; lean_object* v_bitvecState_1147_; lean_object* v_preprocessCaches_1148_; lean_object* v_satSolver_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1232_; 
v_funState_1146_ = lean_ctor_get(v_theoryState_1136_, 0);
v_bitvecState_1147_ = lean_ctor_get(v_theoryState_1136_, 1);
v_preprocessCaches_1148_ = lean_ctor_get(v_theoryState_1136_, 2);
v_satSolver_1149_ = lean_ctor_get(v_theoryState_1136_, 3);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_theoryState_1136_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1151_ = v_theoryState_1136_;
v_isShared_1152_ = v_isSharedCheck_1232_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_satSolver_1149_);
lean_inc(v_preprocessCaches_1148_);
lean_inc(v_bitvecState_1147_);
lean_inc(v_funState_1146_);
lean_dec(v_theoryState_1136_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1232_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 2, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_funState_1146_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_bitvecState_1147_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_satSolver_1149_);
v___x_1155_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 3, v___x_1155_);
v___x_1157_ = v___x_1144_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_satExpr_1137_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_hypQueue_1138_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_usedHyps_1139_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_solverTimeBudgetMs_1141_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_roundBudget_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*6, v_didChange_1140_);
v___x_1157_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_typeAnalysis_1163_; lean_object* v_target_1164_; lean_object* v_hypotheses_1165_; uint8_t v_didChange_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1228_; 
v___x_1158_ = lean_st_ref_put(v_a_725_, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1160_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1160_, 0, v___x_1153_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set(v___x_1160_, 2, v___x_1129_);
lean_ctor_set(v___x_1160_, 3, v___x_1102_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*4, v___x_1108_);
v___x_1161_ = lean_st_mk_ref(v___x_1160_);
v___x_1162_ = lean_st_ref_take(v___x_1161_);
v_typeAnalysis_1163_ = lean_ctor_get(v___x_1162_, 1);
v_target_1164_ = lean_ctor_get(v___x_1162_, 2);
v_hypotheses_1165_ = lean_ctor_get(v___x_1162_, 3);
v_didChange_1166_ = lean_ctor_get_uint8(v___x_1162_, sizeof(void*)*4);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1229_);
v___x_1168_ = v___x_1162_;
v_isShared_1169_ = v_isSharedCheck_1228_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_hypotheses_1165_);
lean_inc(v_target_1164_);
lean_inc(v_typeAnalysis_1163_);
lean_dec(v___x_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1228_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_preprocessCaches_1148_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_preprocessCaches_1148_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_typeAnalysis_1163_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_target_1164_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_hypotheses_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1227_, sizeof(void*)*4, v_didChange_1166_);
v___x_1171_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1172_ = lean_st_ref_put(v___x_1161_, v___x_1171_);
v_sz_1173_ = lean_array_size(v_hypQueue_1092_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1173_, v___x_1174_, v_hypQueue_1092_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
v___x_1177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1176_, v___x_1134_, v___x_1161_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec_ref(v___x_1134_);
lean_dec_ref_known(v___x_1176_, 1);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_st_ref_get(v___x_1161_);
lean_dec(v___x_1161_);
v___x_1180_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1180_ == 0)
{
lean_object* v_caches_1181_; lean_object* v_hypotheses_1182_; lean_object* v___x_1183_; lean_object* v_theoryState_1184_; lean_object* v_satExpr_1185_; lean_object* v_hypQueue_1186_; lean_object* v_usedHyps_1187_; uint8_t v_didChange_1188_; lean_object* v_solverTimeBudgetMs_1189_; lean_object* v_roundBudget_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1224_; 
v_caches_1181_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_caches_1181_);
v_hypotheses_1182_ = lean_ctor_get(v___x_1179_, 3);
lean_inc_ref(v_hypotheses_1182_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_st_ref_take(v_a_725_);
v_theoryState_1184_ = lean_ctor_get(v___x_1183_, 3);
v_satExpr_1185_ = lean_ctor_get(v___x_1183_, 0);
v_hypQueue_1186_ = lean_ctor_get(v___x_1183_, 1);
v_usedHyps_1187_ = lean_ctor_get(v___x_1183_, 2);
v_didChange_1188_ = lean_ctor_get_uint8(v___x_1183_, sizeof(void*)*6);
v_solverTimeBudgetMs_1189_ = lean_ctor_get(v___x_1183_, 4);
v_roundBudget_1190_ = lean_ctor_get(v___x_1183_, 5);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1192_ = v___x_1183_;
v_isShared_1193_ = v_isSharedCheck_1224_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_roundBudget_1190_);
lean_inc(v_solverTimeBudgetMs_1189_);
lean_inc(v_theoryState_1184_);
lean_inc(v_usedHyps_1187_);
lean_inc(v_hypQueue_1186_);
lean_inc(v_satExpr_1185_);
lean_dec(v___x_1183_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1224_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_funState_1194_; lean_object* v_bitvecState_1195_; lean_object* v_satSolver_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1222_; 
v_funState_1194_ = lean_ctor_get(v_theoryState_1184_, 0);
v_bitvecState_1195_ = lean_ctor_get(v_theoryState_1184_, 1);
v_satSolver_1196_ = lean_ctor_get(v_theoryState_1184_, 3);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_theoryState_1184_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_theoryState_1184_, 2);
lean_dec(v_unused_1223_);
v___x_1198_ = v_theoryState_1184_;
v_isShared_1199_ = v_isSharedCheck_1222_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_satSolver_1196_);
lean_inc(v_bitvecState_1195_);
lean_inc(v_funState_1194_);
lean_dec(v_theoryState_1184_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1222_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 2, v_caches_1181_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_funState_1194_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_bitvecState_1195_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_caches_1181_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_satSolver_1196_);
v___x_1201_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 3, v___x_1201_);
v___x_1203_ = v___x_1192_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_satExpr_1185_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_hypQueue_1186_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_usedHyps_1187_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_solverTimeBudgetMs_1189_);
lean_ctor_set(v_reuseFailAlloc_1220_, 5, v_roundBudget_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*6, v_didChange_1188_);
v___x_1203_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; size_t v_sz_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_st_ref_put(v_a_725_, v___x_1203_);
v_sz_1205_ = lean_array_size(v_hypotheses_1182_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1182_, v_sz_1205_, v___x_1174_, v___x_1102_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec_ref(v_hypotheses_1182_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = lean_array_get_size(v_a_1207_);
v___x_1209_ = lean_nat_dec_eq(v___x_1208_, v___x_1101_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v_satExpr_1211_; uint8_t v___x_1212_; 
v___x_1210_ = lean_st_ref_get(v_a_725_);
v_satExpr_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_ref(v_satExpr_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_nat_dec_lt(v___x_1101_, v___x_1208_);
if (v___x_1212_ == 0)
{
lean_dec(v_a_1207_);
v___y_1000_ = v_a_1083_;
v___y_1001_ = v___x_1089_;
v_a_1002_ = v_satExpr_1211_;
goto v___jp_999_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_nat_dec_le(v___x_1208_, v___x_1208_);
if (v___x_1213_ == 0)
{
if (v___x_1212_ == 0)
{
lean_dec(v_a_1207_);
v___y_1000_ = v_a_1083_;
v___y_1001_ = v___x_1089_;
v_a_1002_ = v_satExpr_1211_;
goto v___jp_999_;
}
else
{
size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_usize_of_nat(v___x_1208_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1207_, v___x_1174_, v___x_1214_, v_satExpr_1211_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_1207_);
v___y_1026_ = v_a_1083_;
v___y_1027_ = v___x_1089_;
v___y_1028_ = v___x_1215_;
goto v___jp_1025_;
}
}
else
{
size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_usize_of_nat(v___x_1208_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1207_, v___x_1174_, v___x_1216_, v_satExpr_1211_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_1207_);
v___y_1026_ = v_a_1083_;
v___y_1027_ = v___x_1089_;
v___y_1028_ = v___x_1217_;
goto v___jp_1025_;
}
}
}
else
{
uint8_t v___x_1218_; 
lean_dec(v_a_1207_);
v___x_1218_ = 2;
v___y_994_ = v_a_1083_;
v___y_995_ = v___x_1089_;
v_a_996_ = v___x_1218_;
goto v___jp_993_;
}
}
else
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1206_, 1);
v___y_1021_ = v_a_1083_;
v___y_1022_ = v___x_1089_;
v_a_1023_ = v_a_1219_;
goto v___jp_1020_;
}
}
}
}
}
}
else
{
uint8_t v___x_1225_; 
lean_dec(v___x_1179_);
v___x_1225_ = 0;
v___y_994_ = v_a_1083_;
v___y_995_ = v___x_1089_;
v_a_996_ = v___x_1225_;
goto v___jp_993_;
}
}
else
{
lean_object* v_a_1226_; 
lean_dec(v___x_1161_);
v_a_1226_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1177_, 1);
v___y_1021_ = v_a_1083_;
v___y_1022_ = v___x_1089_;
v_a_1023_ = v_a_1226_;
goto v___jp_1020_;
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
uint8_t v___x_1237_; 
lean_dec_ref(v_hypQueue_1092_);
lean_del_object(v___x_1085_);
v___x_1237_ = 2;
v___y_994_ = v_a_1083_;
v___y_995_ = v___x_1089_;
v_a_996_ = v___x_1237_;
goto v___jp_993_;
}
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_satExpr_1242_; lean_object* v_hypQueue_1243_; lean_object* v_usedHyps_1244_; uint8_t v_didChange_1245_; lean_object* v_theoryState_1246_; lean_object* v_solverTimeBudgetMs_1247_; lean_object* v_roundBudget_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1390_; 
v___x_1240_ = lean_io_get_num_heartbeats();
v___x_1241_ = lean_st_ref_take(v_a_725_);
v_satExpr_1242_ = lean_ctor_get(v___x_1241_, 0);
v_hypQueue_1243_ = lean_ctor_get(v___x_1241_, 1);
v_usedHyps_1244_ = lean_ctor_get(v___x_1241_, 2);
v_didChange_1245_ = lean_ctor_get_uint8(v___x_1241_, sizeof(void*)*6);
v_theoryState_1246_ = lean_ctor_get(v___x_1241_, 3);
v_solverTimeBudgetMs_1247_ = lean_ctor_get(v___x_1241_, 4);
v_roundBudget_1248_ = lean_ctor_get(v___x_1241_, 5);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1250_ = v___x_1241_;
v_isShared_1251_ = v_isSharedCheck_1390_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_roundBudget_1248_);
lean_inc(v_solverTimeBudgetMs_1247_);
lean_inc(v_theoryState_1246_);
lean_inc(v_usedHyps_1244_);
lean_inc(v_hypQueue_1243_);
lean_inc(v_satExpr_1242_);
lean_dec(v___x_1241_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1390_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1254_ = l_Array_append___redArg(v_usedHyps_1244_, v_hypQueue_1243_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 2, v___x_1254_);
lean_ctor_set(v___x_1250_, 1, v___x_1253_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_satExpr_1242_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_theoryState_1246_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_solverTimeBudgetMs_1247_);
lean_ctor_set(v_reuseFailAlloc_1389_, 5, v_roundBudget_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1389_, sizeof(void*)*6, v_didChange_1245_);
v___x_1256_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_st_ref_put(v_a_725_, v___x_1256_);
v___x_1258_ = lean_array_get_size(v_hypQueue_1243_);
v___x_1259_ = lean_nat_dec_eq(v___x_1258_, v___x_1252_);
if (v___x_1259_ == 0)
{
lean_object* v_goal_1260_; lean_object* v_tacticContext_1261_; lean_object* v___x_1262_; lean_object* v_config_1263_; lean_object* v_mode_1264_; lean_object* v_timeout_1265_; uint8_t v_trimProofs_1266_; uint8_t v_binaryProofs_1267_; uint8_t v_acNf_1268_; uint8_t v_andFlattening_1269_; uint8_t v_embeddedConstraintSubst_1270_; uint8_t v_graphviz_1271_; lean_object* v_maxSteps_1272_; uint8_t v_solverMode_1273_; uint8_t v_uf_1274_; lean_object* v_cegarRounds_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1387_; 
v_goal_1260_ = lean_ctor_get(v_a_724_, 0);
v_tacticContext_1261_ = lean_ctor_get(v_a_724_, 2);
lean_inc_ref(v_tacticContext_1261_);
v___x_1262_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1261_);
v_config_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_config_1263_);
v_mode_1264_ = lean_ctor_get(v___x_1262_, 1);
lean_inc(v_mode_1264_);
lean_dec_ref(v___x_1262_);
v_timeout_1265_ = lean_ctor_get(v_config_1263_, 0);
v_trimProofs_1266_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3);
v_binaryProofs_1267_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 1);
v_acNf_1268_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 2);
v_andFlattening_1269_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1270_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 4);
v_graphviz_1271_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 8);
v_maxSteps_1272_ = lean_ctor_get(v_config_1263_, 1);
v_solverMode_1273_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 10);
v_uf_1274_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*3 + 11);
v_cegarRounds_1275_ = lean_ctor_get(v_config_1263_, 2);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_config_1263_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1277_ = v_config_1263_;
v_isShared_1278_ = v_isSharedCheck_1387_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_cegarRounds_1275_);
lean_inc(v_maxSteps_1272_);
lean_inc(v_timeout_1265_);
lean_dec(v_config_1263_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1387_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
lean_inc(v_goal_1260_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_goal_1260_);
v___x_1280_ = v___x_1085_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_goal_1260_);
v___x_1280_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1278_ == 0)
{
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_timeout_1265_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_maxSteps_1272_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_cegarRounds_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3, v_trimProofs_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 1, v_binaryProofs_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 2, v_acNf_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 3, v_andFlattening_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 8, v_graphviz_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 10, v_solverMode_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1385_, sizeof(void*)*3 + 11, v_uf_1274_);
v___x_1282_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_theoryState_1287_; lean_object* v_satExpr_1288_; lean_object* v_hypQueue_1289_; lean_object* v_usedHyps_1290_; uint8_t v_didChange_1291_; lean_object* v_solverTimeBudgetMs_1292_; lean_object* v_roundBudget_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1384_; 
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*3 + 5, v___x_1259_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*3 + 6, v___x_1259_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*3 + 7, v___x_1259_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*3 + 9, v___x_1259_);
v___x_1283_ = lean_box(v___x_1088_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
v___x_1285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1264_, v___x_1282_, v___x_1284_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_st_ref_take(v_a_725_);
v_theoryState_1287_ = lean_ctor_get(v___x_1286_, 3);
v_satExpr_1288_ = lean_ctor_get(v___x_1286_, 0);
v_hypQueue_1289_ = lean_ctor_get(v___x_1286_, 1);
v_usedHyps_1290_ = lean_ctor_get(v___x_1286_, 2);
v_didChange_1291_ = lean_ctor_get_uint8(v___x_1286_, sizeof(void*)*6);
v_solverTimeBudgetMs_1292_ = lean_ctor_get(v___x_1286_, 4);
v_roundBudget_1293_ = lean_ctor_get(v___x_1286_, 5);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1295_ = v___x_1286_;
v_isShared_1296_ = v_isSharedCheck_1384_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_roundBudget_1293_);
lean_inc(v_solverTimeBudgetMs_1292_);
lean_inc(v_theoryState_1287_);
lean_inc(v_usedHyps_1290_);
lean_inc(v_hypQueue_1289_);
lean_inc(v_satExpr_1288_);
lean_dec(v___x_1286_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1384_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_funState_1297_; lean_object* v_bitvecState_1298_; lean_object* v_preprocessCaches_1299_; lean_object* v_satSolver_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1383_; 
v_funState_1297_ = lean_ctor_get(v_theoryState_1287_, 0);
v_bitvecState_1298_ = lean_ctor_get(v_theoryState_1287_, 1);
v_preprocessCaches_1299_ = lean_ctor_get(v_theoryState_1287_, 2);
v_satSolver_1300_ = lean_ctor_get(v_theoryState_1287_, 3);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_theoryState_1287_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1302_ = v_theoryState_1287_;
v_isShared_1303_ = v_isSharedCheck_1383_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_satSolver_1300_);
lean_inc(v_preprocessCaches_1299_);
lean_inc(v_bitvecState_1298_);
lean_inc(v_funState_1297_);
lean_dec(v_theoryState_1287_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1383_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_funState_1297_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_bitvecState_1298_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_satSolver_1300_);
v___x_1306_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 3, v___x_1306_);
v___x_1308_ = v___x_1295_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_satExpr_1288_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_hypQueue_1289_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_usedHyps_1290_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v_solverTimeBudgetMs_1292_);
lean_ctor_set(v_reuseFailAlloc_1381_, 5, v_roundBudget_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*6, v_didChange_1291_);
v___x_1308_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_typeAnalysis_1314_; lean_object* v_target_1315_; lean_object* v_hypotheses_1316_; uint8_t v_didChange_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1379_; 
v___x_1309_ = lean_st_ref_put(v_a_725_, v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1311_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1304_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_ctor_set(v___x_1311_, 2, v___x_1280_);
lean_ctor_set(v___x_1311_, 3, v___x_1253_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*4, v___x_1259_);
v___x_1312_ = lean_st_mk_ref(v___x_1311_);
v___x_1313_ = lean_st_ref_take(v___x_1312_);
v_typeAnalysis_1314_ = lean_ctor_get(v___x_1313_, 1);
v_target_1315_ = lean_ctor_get(v___x_1313_, 2);
v_hypotheses_1316_ = lean_ctor_get(v___x_1313_, 3);
v_didChange_1317_ = lean_ctor_get_uint8(v___x_1313_, sizeof(void*)*4);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1313_, 0);
lean_dec(v_unused_1380_);
v___x_1319_ = v___x_1313_;
v_isShared_1320_ = v_isSharedCheck_1379_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_hypotheses_1316_);
lean_inc(v_target_1315_);
lean_inc(v_typeAnalysis_1314_);
lean_dec(v___x_1313_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1379_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_preprocessCaches_1299_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_preprocessCaches_1299_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_typeAnalysis_1314_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_target_1315_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_hypotheses_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*4, v_didChange_1317_);
v___x_1322_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; size_t v_sz_1324_; size_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = lean_st_ref_put(v___x_1312_, v___x_1322_);
v_sz_1324_ = lean_array_size(v_hypQueue_1243_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1324_, v___x_1325_, v_hypQueue_1243_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
v___x_1328_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1327_, v___x_1285_, v___x_1312_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec_ref(v___x_1285_);
lean_dec_ref_known(v___x_1327_, 1);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_st_ref_get(v___x_1312_);
lean_dec(v___x_1312_);
v___x_1331_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
if (v___x_1331_ == 0)
{
lean_object* v_caches_1332_; lean_object* v_hypotheses_1333_; lean_object* v___x_1334_; lean_object* v_theoryState_1335_; lean_object* v_satExpr_1336_; lean_object* v_hypQueue_1337_; lean_object* v_usedHyps_1338_; uint8_t v_didChange_1339_; lean_object* v_solverTimeBudgetMs_1340_; lean_object* v_roundBudget_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1375_; 
v_caches_1332_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_ref(v_caches_1332_);
v_hypotheses_1333_ = lean_ctor_get(v___x_1330_, 3);
lean_inc_ref(v_hypotheses_1333_);
lean_dec(v___x_1330_);
v___x_1334_ = lean_st_ref_take(v_a_725_);
v_theoryState_1335_ = lean_ctor_get(v___x_1334_, 3);
v_satExpr_1336_ = lean_ctor_get(v___x_1334_, 0);
v_hypQueue_1337_ = lean_ctor_get(v___x_1334_, 1);
v_usedHyps_1338_ = lean_ctor_get(v___x_1334_, 2);
v_didChange_1339_ = lean_ctor_get_uint8(v___x_1334_, sizeof(void*)*6);
v_solverTimeBudgetMs_1340_ = lean_ctor_get(v___x_1334_, 4);
v_roundBudget_1341_ = lean_ctor_get(v___x_1334_, 5);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1343_ = v___x_1334_;
v_isShared_1344_ = v_isSharedCheck_1375_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_roundBudget_1341_);
lean_inc(v_solverTimeBudgetMs_1340_);
lean_inc(v_theoryState_1335_);
lean_inc(v_usedHyps_1338_);
lean_inc(v_hypQueue_1337_);
lean_inc(v_satExpr_1336_);
lean_dec(v___x_1334_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1375_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_funState_1345_; lean_object* v_bitvecState_1346_; lean_object* v_satSolver_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1373_; 
v_funState_1345_ = lean_ctor_get(v_theoryState_1335_, 0);
v_bitvecState_1346_ = lean_ctor_get(v_theoryState_1335_, 1);
v_satSolver_1347_ = lean_ctor_get(v_theoryState_1335_, 3);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_theoryState_1335_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_theoryState_1335_, 2);
lean_dec(v_unused_1374_);
v___x_1349_ = v_theoryState_1335_;
v_isShared_1350_ = v_isSharedCheck_1373_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_satSolver_1347_);
lean_inc(v_bitvecState_1346_);
lean_inc(v_funState_1345_);
lean_dec(v_theoryState_1335_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1373_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 2, v_caches_1332_);
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_funState_1345_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_bitvecState_1346_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_caches_1332_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_satSolver_1347_);
v___x_1352_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 3, v___x_1352_);
v___x_1354_ = v___x_1343_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_satExpr_1336_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_hypQueue_1337_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_usedHyps_1338_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_solverTimeBudgetMs_1340_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_roundBudget_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*6, v_didChange_1339_);
v___x_1354_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; size_t v_sz_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_st_ref_put(v_a_725_, v___x_1354_);
v_sz_1356_ = lean_array_size(v_hypotheses_1333_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1333_, v_sz_1356_, v___x_1325_, v___x_1253_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec_ref(v_hypotheses_1333_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = lean_array_get_size(v_a_1358_);
v___x_1360_ = lean_nat_dec_eq(v___x_1359_, v___x_1252_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v_satExpr_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_st_ref_get(v_a_725_);
v_satExpr_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_satExpr_1362_);
lean_dec(v___x_1361_);
v___x_1363_ = lean_nat_dec_lt(v___x_1252_, v___x_1359_);
if (v___x_1363_ == 0)
{
lean_dec(v_a_1358_);
v___y_1050_ = v_a_1083_;
v___y_1051_ = v___x_1240_;
v_a_1052_ = v_satExpr_1362_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_nat_dec_le(v___x_1359_, v___x_1359_);
if (v___x_1364_ == 0)
{
if (v___x_1363_ == 0)
{
lean_dec(v_a_1358_);
v___y_1050_ = v_a_1083_;
v___y_1051_ = v___x_1240_;
v_a_1052_ = v_satExpr_1362_;
goto v___jp_1049_;
}
else
{
size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_usize_of_nat(v___x_1359_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1358_, v___x_1325_, v___x_1365_, v_satExpr_1362_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_1358_);
v___y_1076_ = v_a_1083_;
v___y_1077_ = v___x_1240_;
v___y_1078_ = v___x_1366_;
goto v___jp_1075_;
}
}
else
{
size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_usize_of_nat(v___x_1359_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1358_, v___x_1325_, v___x_1367_, v_satExpr_1362_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_1358_);
v___y_1076_ = v_a_1083_;
v___y_1077_ = v___x_1240_;
v___y_1078_ = v___x_1368_;
goto v___jp_1075_;
}
}
}
else
{
uint8_t v___x_1369_; 
lean_dec(v_a_1358_);
v___x_1369_ = 2;
v___y_1044_ = v_a_1083_;
v___y_1045_ = v___x_1240_;
v_a_1046_ = v___x_1369_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1357_, 1);
v___y_1071_ = v_a_1083_;
v___y_1072_ = v___x_1240_;
v_a_1073_ = v_a_1370_;
goto v___jp_1070_;
}
}
}
}
}
}
else
{
uint8_t v___x_1376_; 
lean_dec(v___x_1330_);
v___x_1376_ = 0;
v___y_1044_ = v_a_1083_;
v___y_1045_ = v___x_1240_;
v_a_1046_ = v___x_1376_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1377_; 
lean_dec(v___x_1312_);
v_a_1377_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1328_, 1);
v___y_1071_ = v_a_1083_;
v___y_1072_ = v___x_1240_;
v_a_1073_ = v_a_1377_;
goto v___jp_1070_;
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
uint8_t v___x_1388_; 
lean_dec_ref(v_hypQueue_1243_);
lean_del_object(v___x_1085_);
v___x_1388_ = 2;
v___y_1044_ = v_a_1083_;
v___y_1045_ = v___x_1240_;
v_a_1046_ = v___x_1388_;
goto v___jp_1043_;
}
}
}
}
}
}
}
v___jp_739_:
{
lean_object* v___x_742_; lean_object* v_hypQueue_743_; lean_object* v_usedHyps_744_; uint8_t v_didChange_745_; lean_object* v_theoryState_746_; lean_object* v_solverTimeBudgetMs_747_; lean_object* v_roundBudget_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_759_; 
v___x_742_ = lean_st_ref_take(v___y_740_);
v_hypQueue_743_ = lean_ctor_get(v___x_742_, 1);
v_usedHyps_744_ = lean_ctor_get(v___x_742_, 2);
v_didChange_745_ = lean_ctor_get_uint8(v___x_742_, sizeof(void*)*6);
v_theoryState_746_ = lean_ctor_get(v___x_742_, 3);
v_solverTimeBudgetMs_747_ = lean_ctor_get(v___x_742_, 4);
v_roundBudget_748_ = lean_ctor_get(v___x_742_, 5);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_742_, 0);
lean_dec(v_unused_760_);
v___x_750_ = v___x_742_;
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_roundBudget_748_);
lean_inc(v_solverTimeBudgetMs_747_);
lean_inc(v_theoryState_746_);
lean_inc(v_usedHyps_744_);
lean_inc(v_hypQueue_743_);
lean_dec(v___x_742_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_a_741_);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_741_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_hypQueue_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_usedHyps_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_theoryState_746_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_solverTimeBudgetMs_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_roundBudget_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_758_, sizeof(void*)*6, v_didChange_745_);
v___x_753_ = v_reuseFailAlloc_758_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = lean_st_ref_put(v___y_740_, v___x_753_);
v___x_755_ = 1;
v___x_756_ = lean_box(v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
v___jp_761_:
{
if (lean_obj_tag(v___y_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___y_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___y_763_, 1);
v___y_740_ = v___y_762_;
v_a_741_ = v_a_764_;
goto v___jp_739_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___y_763_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___y_763_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___y_763_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___y_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
v___jp_773_:
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_array_get_size(v_hypQueue_774_);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_nat_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v_goal_792_; lean_object* v_tacticContext_793_; lean_object* v___x_794_; lean_object* v_config_795_; lean_object* v_mode_796_; lean_object* v_timeout_797_; uint8_t v_trimProofs_798_; uint8_t v_binaryProofs_799_; uint8_t v_acNf_800_; uint8_t v_andFlattening_801_; uint8_t v_embeddedConstraintSubst_802_; uint8_t v_graphviz_803_; lean_object* v_maxSteps_804_; uint8_t v_solverMode_805_; uint8_t v_uf_806_; lean_object* v_cegarRounds_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_947_; 
v_goal_792_ = lean_ctor_get(v___y_775_, 0);
v_tacticContext_793_ = lean_ctor_get(v___y_775_, 2);
lean_inc_ref(v_tacticContext_793_);
v___x_794_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_793_);
v_config_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_config_795_);
v_mode_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc(v_mode_796_);
lean_dec_ref(v___x_794_);
v_timeout_797_ = lean_ctor_get(v_config_795_, 0);
v_trimProofs_798_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3);
v_binaryProofs_799_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 1);
v_acNf_800_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 2);
v_andFlattening_801_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_802_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 4);
v_graphviz_803_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 8);
v_maxSteps_804_ = lean_ctor_get(v_config_795_, 1);
v_solverMode_805_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 10);
v_uf_806_ = lean_ctor_get_uint8(v_config_795_, sizeof(void*)*3 + 11);
v_cegarRounds_807_ = lean_ctor_get(v_config_795_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_config_795_);
if (v_isSharedCheck_947_ == 0)
{
v___x_809_ = v_config_795_;
v_isShared_810_ = v_isSharedCheck_947_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_cegarRounds_807_);
lean_inc(v_maxSteps_804_);
lean_inc(v_timeout_797_);
lean_dec(v_config_795_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_947_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_goal_792_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_goal_792_);
if (v_isShared_810_ == 0)
{
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_timeout_797_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_maxSteps_804_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_cegarRounds_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3, v_trimProofs_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 1, v_binaryProofs_799_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 2, v_acNf_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 3, v_andFlattening_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 8, v_graphviz_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 10, v_solverMode_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 11, v_uf_806_);
v___x_813_ = v_reuseFailAlloc_946_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_theoryState_817_; lean_object* v_satExpr_818_; lean_object* v_hypQueue_819_; lean_object* v_usedHyps_820_; uint8_t v_didChange_821_; lean_object* v_solverTimeBudgetMs_822_; lean_object* v_roundBudget_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_945_; 
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3 + 5, v___x_791_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3 + 6, v___x_791_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3 + 7, v___x_791_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3 + 9, v___x_791_);
v___x_814_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_815_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_796_, v___x_813_, v___x_814_);
v___x_816_ = lean_st_ref_take(v___y_776_);
v_theoryState_817_ = lean_ctor_get(v___x_816_, 3);
v_satExpr_818_ = lean_ctor_get(v___x_816_, 0);
v_hypQueue_819_ = lean_ctor_get(v___x_816_, 1);
v_usedHyps_820_ = lean_ctor_get(v___x_816_, 2);
v_didChange_821_ = lean_ctor_get_uint8(v___x_816_, sizeof(void*)*6);
v_solverTimeBudgetMs_822_ = lean_ctor_get(v___x_816_, 4);
v_roundBudget_823_ = lean_ctor_get(v___x_816_, 5);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_945_ == 0)
{
v___x_825_ = v___x_816_;
v_isShared_826_ = v_isSharedCheck_945_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_roundBudget_823_);
lean_inc(v_solverTimeBudgetMs_822_);
lean_inc(v_theoryState_817_);
lean_inc(v_usedHyps_820_);
lean_inc(v_hypQueue_819_);
lean_inc(v_satExpr_818_);
lean_dec(v___x_816_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_945_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_funState_827_; lean_object* v_bitvecState_828_; lean_object* v_preprocessCaches_829_; lean_object* v_satSolver_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_944_; 
v_funState_827_ = lean_ctor_get(v_theoryState_817_, 0);
v_bitvecState_828_ = lean_ctor_get(v_theoryState_817_, 1);
v_preprocessCaches_829_ = lean_ctor_get(v_theoryState_817_, 2);
v_satSolver_830_ = lean_ctor_get(v_theoryState_817_, 3);
v_isSharedCheck_944_ = !lean_is_exclusive(v_theoryState_817_);
if (v_isSharedCheck_944_ == 0)
{
v___x_832_ = v_theoryState_817_;
v_isShared_833_ = v_isSharedCheck_944_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_satSolver_830_);
lean_inc(v_preprocessCaches_829_);
lean_inc(v_bitvecState_828_);
lean_inc(v_funState_827_);
lean_dec(v_theoryState_817_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_944_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 2, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_funState_827_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_bitvecState_828_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_satSolver_830_);
v___x_836_ = v_reuseFailAlloc_943_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 3, v___x_836_);
v___x_838_ = v___x_825_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_satExpr_818_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_hypQueue_819_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_usedHyps_820_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_solverTimeBudgetMs_822_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v_roundBudget_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*6, v_didChange_821_);
v___x_838_ = v_reuseFailAlloc_942_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_typeAnalysis_845_; lean_object* v_target_846_; lean_object* v_hypotheses_847_; uint8_t v_didChange_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_940_; 
v___x_839_ = lean_st_ref_put(v___y_776_, v___x_838_);
v___x_840_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_841_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7));
v___x_842_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_842_, 0, v___x_834_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_811_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*4, v___x_791_);
v___x_843_ = lean_st_mk_ref(v___x_842_);
v___x_844_ = lean_st_ref_take(v___x_843_);
v_typeAnalysis_845_ = lean_ctor_get(v___x_844_, 1);
v_target_846_ = lean_ctor_get(v___x_844_, 2);
v_hypotheses_847_ = lean_ctor_get(v___x_844_, 3);
v_didChange_848_ = lean_ctor_get_uint8(v___x_844_, sizeof(void*)*4);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_941_);
v___x_850_ = v___x_844_;
v_isShared_851_ = v_isSharedCheck_940_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_hypotheses_847_);
lean_inc(v_target_846_);
lean_inc(v_typeAnalysis_845_);
lean_dec(v___x_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_940_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_preprocessCaches_829_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_preprocessCaches_829_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_typeAnalysis_845_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_target_846_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_hypotheses_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*4, v_didChange_848_);
v___x_853_ = v_reuseFailAlloc_939_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_854_ = lean_st_ref_put(v___x_843_, v___x_853_);
v_sz_855_ = lean_array_size(v_hypQueue_774_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_855_, v___x_856_, v_hypQueue_774_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
v___x_859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_858_, v___x_815_, v___x_843_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v___x_815_);
lean_dec_ref_known(v___x_858_, 1);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_930_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_930_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_930_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_930_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_st_ref_get(v___x_843_);
lean_dec(v___x_843_);
v___x_865_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_865_ == 0)
{
lean_object* v_caches_866_; lean_object* v_hypotheses_867_; lean_object* v___x_868_; lean_object* v_theoryState_869_; lean_object* v_satExpr_870_; lean_object* v_hypQueue_871_; lean_object* v_usedHyps_872_; uint8_t v_didChange_873_; lean_object* v_solverTimeBudgetMs_874_; lean_object* v_roundBudget_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_924_; 
lean_del_object(v___x_862_);
v_caches_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref(v_caches_866_);
v_hypotheses_867_ = lean_ctor_get(v___x_864_, 3);
lean_inc_ref(v_hypotheses_867_);
lean_dec(v___x_864_);
v___x_868_ = lean_st_ref_take(v___y_776_);
v_theoryState_869_ = lean_ctor_get(v___x_868_, 3);
v_satExpr_870_ = lean_ctor_get(v___x_868_, 0);
v_hypQueue_871_ = lean_ctor_get(v___x_868_, 1);
v_usedHyps_872_ = lean_ctor_get(v___x_868_, 2);
v_didChange_873_ = lean_ctor_get_uint8(v___x_868_, sizeof(void*)*6);
v_solverTimeBudgetMs_874_ = lean_ctor_get(v___x_868_, 4);
v_roundBudget_875_ = lean_ctor_get(v___x_868_, 5);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_924_ == 0)
{
v___x_877_ = v___x_868_;
v_isShared_878_ = v_isSharedCheck_924_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_roundBudget_875_);
lean_inc(v_solverTimeBudgetMs_874_);
lean_inc(v_theoryState_869_);
lean_inc(v_usedHyps_872_);
lean_inc(v_hypQueue_871_);
lean_inc(v_satExpr_870_);
lean_dec(v___x_868_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_924_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_funState_879_; lean_object* v_bitvecState_880_; lean_object* v_satSolver_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_922_; 
v_funState_879_ = lean_ctor_get(v_theoryState_869_, 0);
v_bitvecState_880_ = lean_ctor_get(v_theoryState_869_, 1);
v_satSolver_881_ = lean_ctor_get(v_theoryState_869_, 3);
v_isSharedCheck_922_ = !lean_is_exclusive(v_theoryState_869_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_theoryState_869_, 2);
lean_dec(v_unused_923_);
v___x_883_ = v_theoryState_869_;
v_isShared_884_ = v_isSharedCheck_922_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_satSolver_881_);
lean_inc(v_bitvecState_880_);
lean_inc(v_funState_879_);
lean_dec(v_theoryState_869_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_922_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v_caches_866_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_funState_879_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_bitvecState_880_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_caches_866_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_satSolver_881_);
v___x_886_ = v_reuseFailAlloc_921_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 3, v___x_886_);
v___x_888_ = v___x_877_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_satExpr_870_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_hypQueue_871_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_usedHyps_872_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_solverTimeBudgetMs_874_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_roundBudget_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*6, v_didChange_873_);
v___x_888_ = v_reuseFailAlloc_920_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; size_t v_sz_890_; lean_object* v___x_891_; 
v___x_889_ = lean_st_ref_put(v___y_776_, v___x_888_);
v_sz_890_ = lean_array_size(v_hypotheses_867_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_867_, v_sz_890_, v___x_856_, v___x_841_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v_hypotheses_867_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_911_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_911_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_a_892_);
v___x_897_ = lean_nat_dec_eq(v___x_896_, v___x_790_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v_satExpr_899_; uint8_t v___x_900_; 
lean_del_object(v___x_894_);
v___x_898_ = lean_st_ref_get(v___y_776_);
v_satExpr_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_satExpr_899_);
lean_dec(v___x_898_);
v___x_900_ = lean_nat_dec_lt(v___x_790_, v___x_896_);
if (v___x_900_ == 0)
{
lean_dec(v_a_892_);
v___y_740_ = v___y_776_;
v_a_741_ = v_satExpr_899_;
goto v___jp_739_;
}
else
{
uint8_t v___x_901_; 
v___x_901_ = lean_nat_dec_le(v___x_896_, v___x_896_);
if (v___x_901_ == 0)
{
if (v___x_900_ == 0)
{
lean_dec(v_a_892_);
v___y_740_ = v___y_776_;
v_a_741_ = v_satExpr_899_;
goto v___jp_739_;
}
else
{
size_t v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_usize_of_nat(v___x_896_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_892_, v___x_856_, v___x_902_, v_satExpr_899_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v_a_892_);
v___y_762_ = v___y_776_;
v___y_763_ = v___x_903_;
goto v___jp_761_;
}
}
else
{
size_t v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_usize_of_nat(v___x_896_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_892_, v___x_856_, v___x_904_, v_satExpr_899_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v_a_892_);
v___y_762_ = v___y_776_;
v___y_763_ = v___x_905_;
goto v___jp_761_;
}
}
}
else
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_a_892_);
v___x_906_ = 2;
v___x_907_ = lean_box(v___x_906_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_907_);
v___x_909_ = v___x_894_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_891_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_891_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
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
}
}
}
}
else
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v___x_864_);
v___x_925_ = 0;
v___x_926_ = lean_box(v___x_925_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_926_);
v___x_928_ = v___x_862_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v___x_843_);
v_a_931_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_859_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_859_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
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
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v_hypQueue_774_);
v___x_948_ = 2;
v___x_949_ = lean_box(v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_724_ = stack[0].m_obj;
lean_object* v_a_725_ = stack[1].m_obj;
lean_object* v_a_726_ = stack[2].m_obj;
lean_object* v_a_727_ = stack[3].m_obj;
lean_object* v_a_728_ = stack[4].m_obj;
lean_object* v_a_729_ = stack[5].m_obj;
lean_object* v_a_730_ = stack[6].m_obj;
lean_object* v_a_731_ = stack[7].m_obj;
lean_object* v_a_732_ = stack[8].m_obj;
lean_object* v_a_733_ = stack[9].m_obj;
lean_object* v_a_734_ = stack[10].m_obj;
lean_object* v_a_735_ = stack[11].m_obj;
lean_object* v_a_736_ = stack[12].m_obj;
lean_object* v_a_737_ = stack[13].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1428_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1429_, lean_object* v_msg_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1430_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1430_ = stack[1].m_obj;
lean_object* v___y_1431_ = stack[2].m_obj;
lean_object* v___y_1432_ = stack[3].m_obj;
lean_object* v___y_1433_ = stack[4].m_obj;
lean_object* v___y_1434_ = stack[5].m_obj;
lean_object* v___y_1435_ = stack[6].m_obj;
lean_object* v___y_1436_ = stack[7].m_obj;
lean_object* v___y_1437_ = stack[8].m_obj;
lean_object* v___y_1438_ = stack[9].m_obj;
lean_object* v___y_1439_ = stack[10].m_obj;
lean_object* v___y_1440_ = stack[11].m_obj;
lean_object* v___y_1441_ = stack[12].m_obj;
lean_object* v___y_1442_ = stack[13].m_obj;
lean_object* v___y_1443_ = stack[14].m_obj;
lean_object* v___y_1444_ = stack[15].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_box(0), v_msg_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1448_ = _args[0];
lean_object* v_msg_1449_ = _args[1];
lean_object* v___y_1450_ = _args[2];
lean_object* v___y_1451_ = _args[3];
lean_object* v___y_1452_ = _args[4];
lean_object* v___y_1453_ = _args[5];
lean_object* v___y_1454_ = _args[6];
lean_object* v___y_1455_ = _args[7];
lean_object* v___y_1456_ = _args[8];
lean_object* v___y_1457_ = _args[9];
lean_object* v___y_1458_ = _args[10];
lean_object* v___y_1459_ = _args[11];
lean_object* v___y_1460_ = _args[12];
lean_object* v___y_1461_ = _args[13];
lean_object* v___y_1462_ = _args[14];
lean_object* v___y_1463_ = _args[15];
lean_object* v___y_1464_ = _args[16];
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1448_, v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
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
return v_res_1465_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_1466_, size_t v_i_1467_, size_t v_stop_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_1466_, v_i_1467_, v_stop_1468_, v_b_1469_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1466_ = stack[0].m_obj;
size_t v_i_1467_ = stack[1].m_num;
size_t v_stop_1468_ = stack[2].m_num;
lean_object* v_b_1469_ = stack[3].m_obj;
lean_object* v___y_1470_ = stack[4].m_obj;
lean_object* v___y_1471_ = stack[5].m_obj;
lean_object* v___y_1472_ = stack[6].m_obj;
lean_object* v___y_1473_ = stack[7].m_obj;
lean_object* v___y_1474_ = stack[8].m_obj;
lean_object* v___y_1475_ = stack[9].m_obj;
lean_object* v___y_1476_ = stack[10].m_obj;
lean_object* v___y_1477_ = stack[11].m_obj;
lean_object* v___y_1478_ = stack[12].m_obj;
lean_object* v___y_1479_ = stack[13].m_obj;
lean_object* v___y_1480_ = stack[14].m_obj;
lean_object* v___y_1481_ = stack[15].m_obj;
lean_object* v___y_1482_ = stack[16].m_obj;
lean_object* v___y_1483_ = stack[17].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1466_, v_i_1467_, v_stop_1468_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object** _args){
lean_object* v_as_1487_ = _args[0];
lean_object* v_i_1488_ = _args[1];
lean_object* v_stop_1489_ = _args[2];
lean_object* v_b_1490_ = _args[3];
lean_object* v___y_1491_ = _args[4];
lean_object* v___y_1492_ = _args[5];
lean_object* v___y_1493_ = _args[6];
lean_object* v___y_1494_ = _args[7];
lean_object* v___y_1495_ = _args[8];
lean_object* v___y_1496_ = _args[9];
lean_object* v___y_1497_ = _args[10];
lean_object* v___y_1498_ = _args[11];
lean_object* v___y_1499_ = _args[12];
lean_object* v___y_1500_ = _args[13];
lean_object* v___y_1501_ = _args[14];
lean_object* v___y_1502_ = _args[15];
lean_object* v___y_1503_ = _args[16];
lean_object* v___y_1504_ = _args[17];
lean_object* v___y_1505_ = _args[18];
_start:
{
size_t v_i_boxed_1506_; size_t v_stop_boxed_1507_; lean_object* v_res_1508_; 
v_i_boxed_1506_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_stop_boxed_1507_ = lean_unbox_usize(v_stop_1489_);
lean_dec(v_stop_1489_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1487_, v_i_boxed_1506_, v_stop_boxed_1507_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec_ref(v_as_1487_);
return v_res_1508_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object* v_00_u03b1_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_1510_);
return v___x_1526_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1510_ = stack[1].m_obj;
lean_object* v___y_1511_ = stack[2].m_obj;
lean_object* v___y_1512_ = stack[3].m_obj;
lean_object* v___y_1513_ = stack[4].m_obj;
lean_object* v___y_1514_ = stack[5].m_obj;
lean_object* v___y_1515_ = stack[6].m_obj;
lean_object* v___y_1516_ = stack[7].m_obj;
lean_object* v___y_1517_ = stack[8].m_obj;
lean_object* v___y_1518_ = stack[9].m_obj;
lean_object* v___y_1519_ = stack[10].m_obj;
lean_object* v___y_1520_ = stack[11].m_obj;
lean_object* v___y_1521_ = stack[12].m_obj;
lean_object* v___y_1522_ = stack[13].m_obj;
lean_object* v___y_1523_ = stack[14].m_obj;
lean_object* v___y_1524_ = stack[15].m_obj;
lean_object* v_res_1527_;
v_res_1527_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_box(0), v_x_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
stack->m_obj
 = v_res_1527_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1528_ = _args[0];
lean_object* v_x_1529_ = _args[1];
lean_object* v___y_1530_ = _args[2];
lean_object* v___y_1531_ = _args[3];
lean_object* v___y_1532_ = _args[4];
lean_object* v___y_1533_ = _args[5];
lean_object* v___y_1534_ = _args[6];
lean_object* v___y_1535_ = _args[7];
lean_object* v___y_1536_ = _args[8];
lean_object* v___y_1537_ = _args[9];
lean_object* v___y_1538_ = _args[10];
lean_object* v___y_1539_ = _args[11];
lean_object* v___y_1540_ = _args[12];
lean_object* v___y_1541_ = _args[13];
lean_object* v___y_1542_ = _args[14];
lean_object* v___y_1543_ = _args[15];
lean_object* v___y_1544_ = _args[16];
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(v_00_u03b1_1528_, v_x_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1545_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object* v_oldTraces_1546_, lean_object* v_data_1547_, lean_object* v_ref_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_1546_, v_data_1547_, v_ref_1548_, v_msg_1549_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1546_ = stack[0].m_obj;
lean_object* v_data_1547_ = stack[1].m_obj;
lean_object* v_ref_1548_ = stack[2].m_obj;
lean_object* v_msg_1549_ = stack[3].m_obj;
lean_object* v___y_1550_ = stack[4].m_obj;
lean_object* v___y_1551_ = stack[5].m_obj;
lean_object* v___y_1552_ = stack[6].m_obj;
lean_object* v___y_1553_ = stack[7].m_obj;
lean_object* v___y_1554_ = stack[8].m_obj;
lean_object* v___y_1555_ = stack[9].m_obj;
lean_object* v___y_1556_ = stack[10].m_obj;
lean_object* v___y_1557_ = stack[11].m_obj;
lean_object* v___y_1558_ = stack[12].m_obj;
lean_object* v___y_1559_ = stack[13].m_obj;
lean_object* v___y_1560_ = stack[14].m_obj;
lean_object* v___y_1561_ = stack[15].m_obj;
lean_object* v___y_1562_ = stack[16].m_obj;
lean_object* v___y_1563_ = stack[17].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1546_, v_data_1547_, v_ref_1548_, v_msg_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object** _args){
lean_object* v_oldTraces_1567_ = _args[0];
lean_object* v_data_1568_ = _args[1];
lean_object* v_ref_1569_ = _args[2];
lean_object* v_msg_1570_ = _args[3];
lean_object* v___y_1571_ = _args[4];
lean_object* v___y_1572_ = _args[5];
lean_object* v___y_1573_ = _args[6];
lean_object* v___y_1574_ = _args[7];
lean_object* v___y_1575_ = _args[8];
lean_object* v___y_1576_ = _args[9];
lean_object* v___y_1577_ = _args[10];
lean_object* v___y_1578_ = _args[11];
lean_object* v___y_1579_ = _args[12];
lean_object* v___y_1580_ = _args[13];
lean_object* v___y_1581_ = _args[14];
lean_object* v___y_1582_ = _args[15];
lean_object* v___y_1583_ = _args[16];
lean_object* v___y_1584_ = _args[17];
lean_object* v___y_1585_ = _args[18];
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1567_, v_data_1568_, v_ref_1569_, v_msg_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1586_;
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

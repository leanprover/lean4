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
lean_object* v___y_721_; lean_object* v_a_722_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v_hypQueue_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_toCold_932_; lean_object* v_options_933_; uint8_t v_hasTrace_934_; 
v_toCold_932_ = lean_ctor_get(v_a_717_, 0);
v_options_933_ = lean_ctor_get(v_toCold_932_, 2);
v_hasTrace_934_ = lean_ctor_get_uint8(v_options_933_, sizeof(void*)*1);
if (v_hasTrace_934_ == 0)
{
lean_object* v___x_935_; lean_object* v_satExpr_936_; lean_object* v_hypQueue_937_; lean_object* v_usedHyps_938_; uint8_t v_didChange_939_; lean_object* v_theoryState_940_; lean_object* v_solverTimeBudgetMs_941_; lean_object* v_roundBudget_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v___x_935_ = lean_st_ref_take(v_a_706_);
v_satExpr_936_ = lean_ctor_get(v___x_935_, 0);
v_hypQueue_937_ = lean_ctor_get(v___x_935_, 1);
v_usedHyps_938_ = lean_ctor_get(v___x_935_, 2);
v_didChange_939_ = lean_ctor_get_uint8(v___x_935_, sizeof(void*)*6);
v_theoryState_940_ = lean_ctor_get(v___x_935_, 3);
v_solverTimeBudgetMs_941_ = lean_ctor_get(v___x_935_, 4);
v_roundBudget_942_ = lean_ctor_get(v___x_935_, 5);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_952_ == 0)
{
v___x_944_ = v___x_935_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_roundBudget_942_);
lean_inc(v_solverTimeBudgetMs_941_);
lean_inc(v_theoryState_940_);
lean_inc(v_usedHyps_938_);
lean_inc(v_hypQueue_937_);
lean_inc(v_satExpr_936_);
lean_dec(v___x_935_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_947_ = l_Array_append___redArg(v_usedHyps_938_, v_hypQueue_937_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v___x_947_);
lean_ctor_set(v___x_944_, 1, v___x_946_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_satExpr_936_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_theoryState_940_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_solverTimeBudgetMs_941_);
lean_ctor_set(v_reuseFailAlloc_951_, 5, v_roundBudget_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*6, v_didChange_939_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_st_ref_put(v_a_706_, v___x_949_);
v_hypQueue_755_ = v_hypQueue_937_;
v___y_756_ = v_a_705_;
v___y_757_ = v_a_706_;
v___y_758_ = v_a_707_;
v___y_759_ = v_a_708_;
v___y_760_ = v_a_709_;
v___y_761_ = v_a_710_;
v___y_762_ = v_a_711_;
v___y_763_ = v_a_712_;
v___y_764_ = v_a_713_;
v___y_765_ = v_a_714_;
v___y_766_ = v_a_715_;
v___y_767_ = v_a_716_;
v___y_768_ = v_a_717_;
v___y_769_ = v_a_718_;
goto v___jp_754_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v_a_962_; lean_object* v___y_975_; lean_object* v___y_976_; uint8_t v_a_977_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v_a_983_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v_a_1004_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v_a_1015_; lean_object* v___y_1025_; lean_object* v___y_1026_; uint8_t v_a_1027_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v_a_1033_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_a_1054_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; 
v_inheritedTraceOptions_953_ = lean_ctor_get(v_toCold_932_, 11);
v___f_954_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_955_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_956_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_957_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_958_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_953_, v_options_933_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = l_Lean_trace_profiler;
v___x_1374_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_933_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v_satExpr_1376_; lean_object* v_hypQueue_1377_; lean_object* v_usedHyps_1378_; uint8_t v_didChange_1379_; lean_object* v_theoryState_1380_; lean_object* v_solverTimeBudgetMs_1381_; lean_object* v_roundBudget_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1392_; 
v___x_1375_ = lean_st_ref_take(v_a_706_);
v_satExpr_1376_ = lean_ctor_get(v___x_1375_, 0);
v_hypQueue_1377_ = lean_ctor_get(v___x_1375_, 1);
v_usedHyps_1378_ = lean_ctor_get(v___x_1375_, 2);
v_didChange_1379_ = lean_ctor_get_uint8(v___x_1375_, sizeof(void*)*6);
v_theoryState_1380_ = lean_ctor_get(v___x_1375_, 3);
v_solverTimeBudgetMs_1381_ = lean_ctor_get(v___x_1375_, 4);
v_roundBudget_1382_ = lean_ctor_get(v___x_1375_, 5);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1384_ = v___x_1375_;
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_roundBudget_1382_);
lean_inc(v_solverTimeBudgetMs_1381_);
lean_inc(v_theoryState_1380_);
lean_inc(v_usedHyps_1378_);
lean_inc(v_hypQueue_1377_);
lean_inc(v_satExpr_1376_);
lean_dec(v___x_1375_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1387_ = l_Array_append___redArg(v_usedHyps_1378_, v_hypQueue_1377_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 2, v___x_1387_);
lean_ctor_set(v___x_1384_, 1, v___x_1386_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_satExpr_1376_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_theoryState_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_solverTimeBudgetMs_1381_);
lean_ctor_set(v_reuseFailAlloc_1391_, 5, v_roundBudget_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1391_, sizeof(void*)*6, v_didChange_1379_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_st_ref_put(v_a_706_, v___x_1389_);
v_hypQueue_755_ = v_hypQueue_1377_;
v___y_756_ = v_a_705_;
v___y_757_ = v_a_706_;
v___y_758_ = v_a_707_;
v___y_759_ = v_a_708_;
v___y_760_ = v_a_709_;
v___y_761_ = v_a_710_;
v___y_762_ = v_a_711_;
v___y_763_ = v_a_712_;
v___y_764_ = v_a_713_;
v___y_765_ = v_a_714_;
v___y_766_ = v_a_715_;
v___y_767_ = v_a_716_;
v___y_768_ = v_a_717_;
v___y_769_ = v_a_718_;
goto v___jp_754_;
}
}
}
else
{
goto v___jp_1062_;
}
}
else
{
goto v___jp_1062_;
}
v___jp_959_:
{
lean_object* v___x_963_; double v___x_964_; double v___x_965_; double v___x_966_; double v___x_967_; double v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_963_ = lean_io_mono_nanos_now();
v___x_964_ = lean_float_of_nat(v___y_961_);
v___x_965_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
v___x_966_ = lean_float_div(v___x_964_, v___x_965_);
v___x_967_ = lean_float_of_nat(v___x_963_);
v___x_968_ = lean_float_div(v___x_967_, v___x_965_);
v___x_969_ = lean_box_float(v___x_966_);
v___x_970_ = lean_box_float(v___x_968_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_a_962_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_955_, v_hasTrace_934_, v___x_956_, v_options_933_, v___x_958_, v___y_960_, v___f_954_, v___x_972_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_973_;
}
v___jp_974_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_box(v_a_977_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___y_960_ = v___y_975_;
v___y_961_ = v___y_976_;
v_a_962_ = v___x_979_;
goto v___jp_959_;
}
v___jp_980_:
{
lean_object* v___x_984_; lean_object* v_hypQueue_985_; lean_object* v_usedHyps_986_; uint8_t v_didChange_987_; lean_object* v_theoryState_988_; lean_object* v_solverTimeBudgetMs_989_; lean_object* v_roundBudget_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v___x_984_ = lean_st_ref_take(v_a_706_);
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
v___x_996_ = lean_st_ref_put(v_a_706_, v___x_995_);
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
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_a_1004_);
v___y_960_ = v___y_1002_;
v___y_961_ = v___y_1003_;
v_a_962_ = v___x_1005_;
goto v___jp_959_;
}
v___jp_1006_:
{
if (lean_obj_tag(v___y_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___y_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___y_1009_, 1);
v___y_981_ = v___y_1007_;
v___y_982_ = v___y_1008_;
v_a_983_ = v_a_1010_;
goto v___jp_980_;
}
else
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v___y_1009_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___y_1009_, 1);
v___y_1002_ = v___y_1007_;
v___y_1003_ = v___y_1008_;
v_a_1004_ = v_a_1011_;
goto v___jp_1001_;
}
}
v___jp_1012_:
{
lean_object* v___x_1016_; double v___x_1017_; double v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1016_ = lean_io_get_num_heartbeats();
v___x_1017_ = lean_float_of_nat(v___y_1013_);
v___x_1018_ = lean_float_of_nat(v___x_1016_);
v___x_1019_ = lean_box_float(v___x_1017_);
v___x_1020_ = lean_box_float(v___x_1018_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_a_1015_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_955_, v_hasTrace_934_, v___x_956_, v_options_933_, v___x_958_, v___y_1014_, v___f_954_, v___x_1022_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_1023_;
}
v___jp_1024_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_box(v_a_1027_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
v___y_1013_ = v___y_1025_;
v___y_1014_ = v___y_1026_;
v_a_1015_ = v___x_1029_;
goto v___jp_1012_;
}
v___jp_1030_:
{
lean_object* v___x_1034_; lean_object* v_hypQueue_1035_; lean_object* v_usedHyps_1036_; uint8_t v_didChange_1037_; lean_object* v_theoryState_1038_; lean_object* v_solverTimeBudgetMs_1039_; lean_object* v_roundBudget_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1049_; 
v___x_1034_ = lean_st_ref_take(v_a_706_);
v_hypQueue_1035_ = lean_ctor_get(v___x_1034_, 1);
v_usedHyps_1036_ = lean_ctor_get(v___x_1034_, 2);
v_didChange_1037_ = lean_ctor_get_uint8(v___x_1034_, sizeof(void*)*6);
v_theoryState_1038_ = lean_ctor_get(v___x_1034_, 3);
v_solverTimeBudgetMs_1039_ = lean_ctor_get(v___x_1034_, 4);
v_roundBudget_1040_ = lean_ctor_get(v___x_1034_, 5);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1050_);
v___x_1042_ = v___x_1034_;
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_roundBudget_1040_);
lean_inc(v_solverTimeBudgetMs_1039_);
lean_inc(v_theoryState_1038_);
lean_inc(v_usedHyps_1036_);
lean_inc(v_hypQueue_1035_);
lean_dec(v___x_1034_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_a_1033_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_hypQueue_1035_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_usedHyps_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_theoryState_1038_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_solverTimeBudgetMs_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 5, v_roundBudget_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, sizeof(void*)*6, v_didChange_1037_);
v___x_1045_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_st_ref_put(v_a_706_, v___x_1045_);
v___x_1047_ = 1;
v___y_1025_ = v___y_1031_;
v___y_1026_ = v___y_1032_;
v_a_1027_ = v___x_1047_;
goto v___jp_1024_;
}
}
}
v___jp_1051_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1054_);
v___y_1013_ = v___y_1052_;
v___y_1014_ = v___y_1053_;
v_a_1015_ = v___x_1055_;
goto v___jp_1012_;
}
v___jp_1056_:
{
if (lean_obj_tag(v___y_1059_) == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___y_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___y_1059_, 1);
v___y_1031_ = v___y_1057_;
v___y_1032_ = v___y_1058_;
v_a_1033_ = v_a_1060_;
goto v___jp_1030_;
}
else
{
lean_object* v_a_1061_; 
v_a_1061_ = lean_ctor_get(v___y_1059_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___y_1059_, 1);
v___y_1052_ = v___y_1057_;
v___y_1053_ = v___y_1058_;
v_a_1054_ = v_a_1061_;
goto v___jp_1051_;
}
}
v___jp_1062_:
{
lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1372_; 
v___x_1063_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v_a_718_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1372_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1372_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1069_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_933_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_satExpr_1072_; lean_object* v_hypQueue_1073_; lean_object* v_usedHyps_1074_; uint8_t v_didChange_1075_; lean_object* v_theoryState_1076_; lean_object* v_solverTimeBudgetMs_1077_; lean_object* v_roundBudget_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1220_; 
v___x_1070_ = lean_io_mono_nanos_now();
v___x_1071_ = lean_st_ref_take(v_a_706_);
v_satExpr_1072_ = lean_ctor_get(v___x_1071_, 0);
v_hypQueue_1073_ = lean_ctor_get(v___x_1071_, 1);
v_usedHyps_1074_ = lean_ctor_get(v___x_1071_, 2);
v_didChange_1075_ = lean_ctor_get_uint8(v___x_1071_, sizeof(void*)*6);
v_theoryState_1076_ = lean_ctor_get(v___x_1071_, 3);
v_solverTimeBudgetMs_1077_ = lean_ctor_get(v___x_1071_, 4);
v_roundBudget_1078_ = lean_ctor_get(v___x_1071_, 5);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1080_ = v___x_1071_;
v_isShared_1081_ = v_isSharedCheck_1220_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_roundBudget_1078_);
lean_inc(v_solverTimeBudgetMs_1077_);
lean_inc(v_theoryState_1076_);
lean_inc(v_usedHyps_1074_);
lean_inc(v_hypQueue_1073_);
lean_inc(v_satExpr_1072_);
lean_dec(v___x_1071_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1220_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1084_ = l_Array_append___redArg(v_usedHyps_1074_, v_hypQueue_1073_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 2, v___x_1084_);
lean_ctor_set(v___x_1080_, 1, v___x_1083_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_satExpr_1072_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_theoryState_1076_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_solverTimeBudgetMs_1077_);
lean_ctor_set(v_reuseFailAlloc_1219_, 5, v_roundBudget_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*6, v_didChange_1075_);
v___x_1086_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_st_ref_put(v_a_706_, v___x_1086_);
v___x_1088_ = lean_array_get_size(v_hypQueue_1073_);
v___x_1089_ = lean_nat_dec_eq(v___x_1088_, v___x_1082_);
if (v___x_1089_ == 0)
{
lean_object* v_goal_1090_; lean_object* v_tacticContext_1091_; lean_object* v___x_1092_; lean_object* v_config_1093_; lean_object* v_mode_1094_; lean_object* v_timeout_1095_; uint8_t v_trimProofs_1096_; uint8_t v_binaryProofs_1097_; uint8_t v_acNf_1098_; uint8_t v_andFlattening_1099_; uint8_t v_embeddedConstraintSubst_1100_; uint8_t v_graphviz_1101_; lean_object* v_maxSteps_1102_; uint8_t v_solverMode_1103_; uint8_t v_uf_1104_; lean_object* v_cegarRounds_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1217_; 
v_goal_1090_ = lean_ctor_get(v_a_705_, 0);
v_tacticContext_1091_ = lean_ctor_get(v_a_705_, 2);
lean_inc_ref(v_tacticContext_1091_);
v___x_1092_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1091_);
v_config_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc_ref(v_config_1093_);
v_mode_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_mode_1094_);
lean_dec_ref(v___x_1092_);
v_timeout_1095_ = lean_ctor_get(v_config_1093_, 0);
v_trimProofs_1096_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3);
v_binaryProofs_1097_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 1);
v_acNf_1098_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 2);
v_andFlattening_1099_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1100_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 4);
v_graphviz_1101_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 8);
v_maxSteps_1102_ = lean_ctor_get(v_config_1093_, 1);
v_solverMode_1103_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 10);
v_uf_1104_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*3 + 11);
v_cegarRounds_1105_ = lean_ctor_get(v_config_1093_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_config_1093_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1107_ = v_config_1093_;
v_isShared_1108_ = v_isSharedCheck_1217_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_cegarRounds_1105_);
lean_inc(v_maxSteps_1102_);
lean_inc(v_timeout_1095_);
lean_dec(v_config_1093_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1217_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
lean_inc(v_goal_1090_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_goal_1090_);
v___x_1110_ = v___x_1066_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_goal_1090_);
v___x_1110_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1108_ == 0)
{
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_timeout_1095_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_maxSteps_1102_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_cegarRounds_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3, v_trimProofs_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 1, v_binaryProofs_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 2, v_acNf_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 3, v_andFlattening_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 8, v_graphviz_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 10, v_solverMode_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*3 + 11, v_uf_1104_);
v___x_1112_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_theoryState_1117_; lean_object* v_satExpr_1118_; lean_object* v_hypQueue_1119_; lean_object* v_usedHyps_1120_; uint8_t v_didChange_1121_; lean_object* v_solverTimeBudgetMs_1122_; lean_object* v_roundBudget_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1214_; 
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*3 + 5, v___x_1089_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*3 + 6, v___x_1089_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*3 + 7, v___x_1089_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*3 + 9, v___x_1089_);
v___x_1113_ = lean_box(v_hasTrace_934_);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1094_, v___x_1112_, v___x_1114_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = lean_st_ref_take(v_a_706_);
v_theoryState_1117_ = lean_ctor_get(v___x_1116_, 3);
v_satExpr_1118_ = lean_ctor_get(v___x_1116_, 0);
v_hypQueue_1119_ = lean_ctor_get(v___x_1116_, 1);
v_usedHyps_1120_ = lean_ctor_get(v___x_1116_, 2);
v_didChange_1121_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*6);
v_solverTimeBudgetMs_1122_ = lean_ctor_get(v___x_1116_, 4);
v_roundBudget_1123_ = lean_ctor_get(v___x_1116_, 5);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1125_ = v___x_1116_;
v_isShared_1126_ = v_isSharedCheck_1214_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_roundBudget_1123_);
lean_inc(v_solverTimeBudgetMs_1122_);
lean_inc(v_theoryState_1117_);
lean_inc(v_usedHyps_1120_);
lean_inc(v_hypQueue_1119_);
lean_inc(v_satExpr_1118_);
lean_dec(v___x_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1214_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_funState_1127_; lean_object* v_bitvecState_1128_; lean_object* v_preprocessCaches_1129_; lean_object* v_satSolver_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1213_; 
v_funState_1127_ = lean_ctor_get(v_theoryState_1117_, 0);
v_bitvecState_1128_ = lean_ctor_get(v_theoryState_1117_, 1);
v_preprocessCaches_1129_ = lean_ctor_get(v_theoryState_1117_, 2);
v_satSolver_1130_ = lean_ctor_get(v_theoryState_1117_, 3);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_theoryState_1117_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1132_ = v_theoryState_1117_;
v_isShared_1133_ = v_isSharedCheck_1213_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_satSolver_1130_);
lean_inc(v_preprocessCaches_1129_);
lean_inc(v_bitvecState_1128_);
lean_inc(v_funState_1127_);
lean_dec(v_theoryState_1117_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1213_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 2, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_funState_1127_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_bitvecState_1128_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_satSolver_1130_);
v___x_1136_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 3, v___x_1136_);
v___x_1138_ = v___x_1125_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_satExpr_1118_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_hypQueue_1119_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_usedHyps_1120_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_solverTimeBudgetMs_1122_);
lean_ctor_set(v_reuseFailAlloc_1211_, 5, v_roundBudget_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*6, v_didChange_1121_);
v___x_1138_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_typeAnalysis_1144_; lean_object* v_target_1145_; lean_object* v_hypotheses_1146_; uint8_t v_didChange_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1209_; 
v___x_1139_ = lean_st_ref_put(v_a_706_, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1141_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1141_, 0, v___x_1134_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
lean_ctor_set(v___x_1141_, 2, v___x_1110_);
lean_ctor_set(v___x_1141_, 3, v___x_1083_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*4, v___x_1089_);
v___x_1142_ = lean_st_mk_ref(v___x_1141_);
v___x_1143_ = lean_st_ref_take(v___x_1142_);
v_typeAnalysis_1144_ = lean_ctor_get(v___x_1143_, 1);
v_target_1145_ = lean_ctor_get(v___x_1143_, 2);
v_hypotheses_1146_ = lean_ctor_get(v___x_1143_, 3);
v_didChange_1147_ = lean_ctor_get_uint8(v___x_1143_, sizeof(void*)*4);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1143_, 0);
lean_dec(v_unused_1210_);
v___x_1149_ = v___x_1143_;
v_isShared_1150_ = v_isSharedCheck_1209_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_hypotheses_1146_);
lean_inc(v_target_1145_);
lean_inc(v_typeAnalysis_1144_);
lean_dec(v___x_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1209_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_preprocessCaches_1129_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_preprocessCaches_1129_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_typeAnalysis_1144_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_target_1145_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_hypotheses_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*4, v_didChange_1147_);
v___x_1152_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; size_t v_sz_1154_; size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1153_ = lean_st_ref_put(v___x_1142_, v___x_1152_);
v_sz_1154_ = lean_array_size(v_hypQueue_1073_);
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1154_, v___x_1155_, v_hypQueue_1073_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
v___x_1158_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1157_, v___x_1115_, v___x_1142_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v___x_1115_);
lean_dec_ref_known(v___x_1157_, 1);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_st_ref_get(v___x_1142_);
lean_dec(v___x_1142_);
v___x_1161_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
if (v___x_1161_ == 0)
{
lean_object* v_caches_1162_; lean_object* v_hypotheses_1163_; lean_object* v___x_1164_; lean_object* v_theoryState_1165_; lean_object* v_satExpr_1166_; lean_object* v_hypQueue_1167_; lean_object* v_usedHyps_1168_; uint8_t v_didChange_1169_; lean_object* v_solverTimeBudgetMs_1170_; lean_object* v_roundBudget_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1205_; 
v_caches_1162_ = lean_ctor_get(v___x_1160_, 0);
lean_inc_ref(v_caches_1162_);
v_hypotheses_1163_ = lean_ctor_get(v___x_1160_, 3);
lean_inc_ref(v_hypotheses_1163_);
lean_dec(v___x_1160_);
v___x_1164_ = lean_st_ref_take(v_a_706_);
v_theoryState_1165_ = lean_ctor_get(v___x_1164_, 3);
v_satExpr_1166_ = lean_ctor_get(v___x_1164_, 0);
v_hypQueue_1167_ = lean_ctor_get(v___x_1164_, 1);
v_usedHyps_1168_ = lean_ctor_get(v___x_1164_, 2);
v_didChange_1169_ = lean_ctor_get_uint8(v___x_1164_, sizeof(void*)*6);
v_solverTimeBudgetMs_1170_ = lean_ctor_get(v___x_1164_, 4);
v_roundBudget_1171_ = lean_ctor_get(v___x_1164_, 5);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1173_ = v___x_1164_;
v_isShared_1174_ = v_isSharedCheck_1205_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_roundBudget_1171_);
lean_inc(v_solverTimeBudgetMs_1170_);
lean_inc(v_theoryState_1165_);
lean_inc(v_usedHyps_1168_);
lean_inc(v_hypQueue_1167_);
lean_inc(v_satExpr_1166_);
lean_dec(v___x_1164_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1205_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_funState_1175_; lean_object* v_bitvecState_1176_; lean_object* v_satSolver_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1203_; 
v_funState_1175_ = lean_ctor_get(v_theoryState_1165_, 0);
v_bitvecState_1176_ = lean_ctor_get(v_theoryState_1165_, 1);
v_satSolver_1177_ = lean_ctor_get(v_theoryState_1165_, 3);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_theoryState_1165_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_theoryState_1165_, 2);
lean_dec(v_unused_1204_);
v___x_1179_ = v_theoryState_1165_;
v_isShared_1180_ = v_isSharedCheck_1203_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_satSolver_1177_);
lean_inc(v_bitvecState_1176_);
lean_inc(v_funState_1175_);
lean_dec(v_theoryState_1165_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1203_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 2, v_caches_1162_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_funState_1175_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_bitvecState_1176_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_caches_1162_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_satSolver_1177_);
v___x_1182_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 3, v___x_1182_);
v___x_1184_ = v___x_1173_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_satExpr_1166_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_hypQueue_1167_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_usedHyps_1168_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_solverTimeBudgetMs_1170_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v_roundBudget_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1201_, sizeof(void*)*6, v_didChange_1169_);
v___x_1184_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; size_t v_sz_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_st_ref_put(v_a_706_, v___x_1184_);
v_sz_1186_ = lean_array_size(v_hypotheses_1163_);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1163_, v_sz_1186_, v___x_1155_, v___x_1083_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v_hypotheses_1163_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = lean_array_get_size(v_a_1188_);
v___x_1190_ = lean_nat_dec_eq(v___x_1189_, v___x_1082_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v_satExpr_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_st_ref_get(v_a_706_);
v_satExpr_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_satExpr_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_nat_dec_lt(v___x_1082_, v___x_1189_);
if (v___x_1193_ == 0)
{
lean_dec(v_a_1188_);
v___y_981_ = v_a_1064_;
v___y_982_ = v___x_1070_;
v_a_983_ = v_satExpr_1192_;
goto v___jp_980_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_nat_dec_le(v___x_1189_, v___x_1189_);
if (v___x_1194_ == 0)
{
if (v___x_1193_ == 0)
{
lean_dec(v_a_1188_);
v___y_981_ = v_a_1064_;
v___y_982_ = v___x_1070_;
v_a_983_ = v_satExpr_1192_;
goto v___jp_980_;
}
else
{
size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_usize_of_nat(v___x_1189_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1188_, v___x_1155_, v___x_1195_, v_satExpr_1192_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1188_);
v___y_1007_ = v_a_1064_;
v___y_1008_ = v___x_1070_;
v___y_1009_ = v___x_1196_;
goto v___jp_1006_;
}
}
else
{
size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_usize_of_nat(v___x_1189_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1188_, v___x_1155_, v___x_1197_, v_satExpr_1192_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1188_);
v___y_1007_ = v_a_1064_;
v___y_1008_ = v___x_1070_;
v___y_1009_ = v___x_1198_;
goto v___jp_1006_;
}
}
}
else
{
uint8_t v___x_1199_; 
lean_dec(v_a_1188_);
v___x_1199_ = 2;
v___y_975_ = v_a_1064_;
v___y_976_ = v___x_1070_;
v_a_977_ = v___x_1199_;
goto v___jp_974_;
}
}
else
{
lean_object* v_a_1200_; 
v_a_1200_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1187_, 1);
v___y_1002_ = v_a_1064_;
v___y_1003_ = v___x_1070_;
v_a_1004_ = v_a_1200_;
goto v___jp_1001_;
}
}
}
}
}
}
else
{
uint8_t v___x_1206_; 
lean_dec(v___x_1160_);
v___x_1206_ = 0;
v___y_975_ = v_a_1064_;
v___y_976_ = v___x_1070_;
v_a_977_ = v___x_1206_;
goto v___jp_974_;
}
}
else
{
lean_object* v_a_1207_; 
lean_dec(v___x_1142_);
v_a_1207_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1158_, 1);
v___y_1002_ = v_a_1064_;
v___y_1003_ = v___x_1070_;
v_a_1004_ = v_a_1207_;
goto v___jp_1001_;
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
uint8_t v___x_1218_; 
lean_dec_ref(v_hypQueue_1073_);
lean_del_object(v___x_1066_);
v___x_1218_ = 2;
v___y_975_ = v_a_1064_;
v___y_976_ = v___x_1070_;
v_a_977_ = v___x_1218_;
goto v___jp_974_;
}
}
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_satExpr_1223_; lean_object* v_hypQueue_1224_; lean_object* v_usedHyps_1225_; uint8_t v_didChange_1226_; lean_object* v_theoryState_1227_; lean_object* v_solverTimeBudgetMs_1228_; lean_object* v_roundBudget_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1371_; 
v___x_1221_ = lean_io_get_num_heartbeats();
v___x_1222_ = lean_st_ref_take(v_a_706_);
v_satExpr_1223_ = lean_ctor_get(v___x_1222_, 0);
v_hypQueue_1224_ = lean_ctor_get(v___x_1222_, 1);
v_usedHyps_1225_ = lean_ctor_get(v___x_1222_, 2);
v_didChange_1226_ = lean_ctor_get_uint8(v___x_1222_, sizeof(void*)*6);
v_theoryState_1227_ = lean_ctor_get(v___x_1222_, 3);
v_solverTimeBudgetMs_1228_ = lean_ctor_get(v___x_1222_, 4);
v_roundBudget_1229_ = lean_ctor_get(v___x_1222_, 5);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1231_ = v___x_1222_;
v_isShared_1232_ = v_isSharedCheck_1371_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_roundBudget_1229_);
lean_inc(v_solverTimeBudgetMs_1228_);
lean_inc(v_theoryState_1227_);
lean_inc(v_usedHyps_1225_);
lean_inc(v_hypQueue_1224_);
lean_inc(v_satExpr_1223_);
lean_dec(v___x_1222_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1371_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1235_ = l_Array_append___redArg(v_usedHyps_1225_, v_hypQueue_1224_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 2, v___x_1235_);
lean_ctor_set(v___x_1231_, 1, v___x_1234_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_satExpr_1223_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_theoryState_1227_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_solverTimeBudgetMs_1228_);
lean_ctor_set(v_reuseFailAlloc_1370_, 5, v_roundBudget_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*6, v_didChange_1226_);
v___x_1237_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_st_ref_put(v_a_706_, v___x_1237_);
v___x_1239_ = lean_array_get_size(v_hypQueue_1224_);
v___x_1240_ = lean_nat_dec_eq(v___x_1239_, v___x_1233_);
if (v___x_1240_ == 0)
{
lean_object* v_goal_1241_; lean_object* v_tacticContext_1242_; lean_object* v___x_1243_; lean_object* v_config_1244_; lean_object* v_mode_1245_; lean_object* v_timeout_1246_; uint8_t v_trimProofs_1247_; uint8_t v_binaryProofs_1248_; uint8_t v_acNf_1249_; uint8_t v_andFlattening_1250_; uint8_t v_embeddedConstraintSubst_1251_; uint8_t v_graphviz_1252_; lean_object* v_maxSteps_1253_; uint8_t v_solverMode_1254_; uint8_t v_uf_1255_; lean_object* v_cegarRounds_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1368_; 
v_goal_1241_ = lean_ctor_get(v_a_705_, 0);
v_tacticContext_1242_ = lean_ctor_get(v_a_705_, 2);
lean_inc_ref(v_tacticContext_1242_);
v___x_1243_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1242_);
v_config_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_config_1244_);
v_mode_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_mode_1245_);
lean_dec_ref(v___x_1243_);
v_timeout_1246_ = lean_ctor_get(v_config_1244_, 0);
v_trimProofs_1247_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3);
v_binaryProofs_1248_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 1);
v_acNf_1249_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 2);
v_andFlattening_1250_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1251_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 4);
v_graphviz_1252_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 8);
v_maxSteps_1253_ = lean_ctor_get(v_config_1244_, 1);
v_solverMode_1254_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 10);
v_uf_1255_ = lean_ctor_get_uint8(v_config_1244_, sizeof(void*)*3 + 11);
v_cegarRounds_1256_ = lean_ctor_get(v_config_1244_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_config_1244_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1258_ = v_config_1244_;
v_isShared_1259_ = v_isSharedCheck_1368_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_cegarRounds_1256_);
lean_inc(v_maxSteps_1253_);
lean_inc(v_timeout_1246_);
lean_dec(v_config_1244_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1368_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
lean_inc(v_goal_1241_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_goal_1241_);
v___x_1261_ = v___x_1066_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_goal_1241_);
v___x_1261_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1259_ == 0)
{
v___x_1263_ = v___x_1258_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_timeout_1246_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_maxSteps_1253_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_cegarRounds_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3, v_trimProofs_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 1, v_binaryProofs_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 2, v_acNf_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 3, v_andFlattening_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 8, v_graphviz_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 10, v_solverMode_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1366_, sizeof(void*)*3 + 11, v_uf_1255_);
v___x_1263_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_theoryState_1268_; lean_object* v_satExpr_1269_; lean_object* v_hypQueue_1270_; lean_object* v_usedHyps_1271_; uint8_t v_didChange_1272_; lean_object* v_solverTimeBudgetMs_1273_; lean_object* v_roundBudget_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1365_; 
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*3 + 5, v___x_1240_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*3 + 6, v___x_1240_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*3 + 7, v___x_1240_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*3 + 9, v___x_1240_);
v___x_1264_ = lean_box(v___x_1069_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1245_, v___x_1263_, v___x_1265_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = lean_st_ref_take(v_a_706_);
v_theoryState_1268_ = lean_ctor_get(v___x_1267_, 3);
v_satExpr_1269_ = lean_ctor_get(v___x_1267_, 0);
v_hypQueue_1270_ = lean_ctor_get(v___x_1267_, 1);
v_usedHyps_1271_ = lean_ctor_get(v___x_1267_, 2);
v_didChange_1272_ = lean_ctor_get_uint8(v___x_1267_, sizeof(void*)*6);
v_solverTimeBudgetMs_1273_ = lean_ctor_get(v___x_1267_, 4);
v_roundBudget_1274_ = lean_ctor_get(v___x_1267_, 5);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1276_ = v___x_1267_;
v_isShared_1277_ = v_isSharedCheck_1365_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_roundBudget_1274_);
lean_inc(v_solverTimeBudgetMs_1273_);
lean_inc(v_theoryState_1268_);
lean_inc(v_usedHyps_1271_);
lean_inc(v_hypQueue_1270_);
lean_inc(v_satExpr_1269_);
lean_dec(v___x_1267_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1365_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_funState_1278_; lean_object* v_bitvecState_1279_; lean_object* v_preprocessCaches_1280_; lean_object* v_satSolver_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1364_; 
v_funState_1278_ = lean_ctor_get(v_theoryState_1268_, 0);
v_bitvecState_1279_ = lean_ctor_get(v_theoryState_1268_, 1);
v_preprocessCaches_1280_ = lean_ctor_get(v_theoryState_1268_, 2);
v_satSolver_1281_ = lean_ctor_get(v_theoryState_1268_, 3);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_theoryState_1268_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1283_ = v_theoryState_1268_;
v_isShared_1284_ = v_isSharedCheck_1364_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_satSolver_1281_);
lean_inc(v_preprocessCaches_1280_);
lean_inc(v_bitvecState_1279_);
lean_inc(v_funState_1278_);
lean_dec(v_theoryState_1268_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1364_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 2, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_funState_1278_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_bitvecState_1279_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_satSolver_1281_);
v___x_1287_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 3, v___x_1287_);
v___x_1289_ = v___x_1276_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_satExpr_1269_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_hypQueue_1270_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_usedHyps_1271_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_solverTimeBudgetMs_1273_);
lean_ctor_set(v_reuseFailAlloc_1362_, 5, v_roundBudget_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*6, v_didChange_1272_);
v___x_1289_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_typeAnalysis_1295_; lean_object* v_target_1296_; lean_object* v_hypotheses_1297_; uint8_t v_didChange_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1360_; 
v___x_1290_ = lean_st_ref_put(v_a_706_, v___x_1289_);
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1292_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1285_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set(v___x_1292_, 2, v___x_1261_);
lean_ctor_set(v___x_1292_, 3, v___x_1234_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*4, v___x_1240_);
v___x_1293_ = lean_st_mk_ref(v___x_1292_);
v___x_1294_ = lean_st_ref_take(v___x_1293_);
v_typeAnalysis_1295_ = lean_ctor_get(v___x_1294_, 1);
v_target_1296_ = lean_ctor_get(v___x_1294_, 2);
v_hypotheses_1297_ = lean_ctor_get(v___x_1294_, 3);
v_didChange_1298_ = lean_ctor_get_uint8(v___x_1294_, sizeof(void*)*4);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1294_, 0);
lean_dec(v_unused_1361_);
v___x_1300_ = v___x_1294_;
v_isShared_1301_ = v_isSharedCheck_1360_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_hypotheses_1297_);
lean_inc(v_target_1296_);
lean_inc(v_typeAnalysis_1295_);
lean_dec(v___x_1294_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1360_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_preprocessCaches_1280_);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_preprocessCaches_1280_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_typeAnalysis_1295_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_target_1296_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_hypotheses_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1359_, sizeof(void*)*4, v_didChange_1298_);
v___x_1303_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; size_t v_sz_1305_; size_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = lean_st_ref_put(v___x_1293_, v___x_1303_);
v_sz_1305_ = lean_array_size(v_hypQueue_1224_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1305_, v___x_1306_, v_hypQueue_1224_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
v___x_1309_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1308_, v___x_1266_, v___x_1293_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v___x_1266_);
lean_dec_ref_known(v___x_1308_, 1);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = lean_st_ref_get(v___x_1293_);
lean_dec(v___x_1293_);
v___x_1312_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
if (v___x_1312_ == 0)
{
lean_object* v_caches_1313_; lean_object* v_hypotheses_1314_; lean_object* v___x_1315_; lean_object* v_theoryState_1316_; lean_object* v_satExpr_1317_; lean_object* v_hypQueue_1318_; lean_object* v_usedHyps_1319_; uint8_t v_didChange_1320_; lean_object* v_solverTimeBudgetMs_1321_; lean_object* v_roundBudget_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1356_; 
v_caches_1313_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_ref(v_caches_1313_);
v_hypotheses_1314_ = lean_ctor_get(v___x_1311_, 3);
lean_inc_ref(v_hypotheses_1314_);
lean_dec(v___x_1311_);
v___x_1315_ = lean_st_ref_take(v_a_706_);
v_theoryState_1316_ = lean_ctor_get(v___x_1315_, 3);
v_satExpr_1317_ = lean_ctor_get(v___x_1315_, 0);
v_hypQueue_1318_ = lean_ctor_get(v___x_1315_, 1);
v_usedHyps_1319_ = lean_ctor_get(v___x_1315_, 2);
v_didChange_1320_ = lean_ctor_get_uint8(v___x_1315_, sizeof(void*)*6);
v_solverTimeBudgetMs_1321_ = lean_ctor_get(v___x_1315_, 4);
v_roundBudget_1322_ = lean_ctor_get(v___x_1315_, 5);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1324_ = v___x_1315_;
v_isShared_1325_ = v_isSharedCheck_1356_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_roundBudget_1322_);
lean_inc(v_solverTimeBudgetMs_1321_);
lean_inc(v_theoryState_1316_);
lean_inc(v_usedHyps_1319_);
lean_inc(v_hypQueue_1318_);
lean_inc(v_satExpr_1317_);
lean_dec(v___x_1315_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1356_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v_funState_1326_; lean_object* v_bitvecState_1327_; lean_object* v_satSolver_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1354_; 
v_funState_1326_ = lean_ctor_get(v_theoryState_1316_, 0);
v_bitvecState_1327_ = lean_ctor_get(v_theoryState_1316_, 1);
v_satSolver_1328_ = lean_ctor_get(v_theoryState_1316_, 3);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_theoryState_1316_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_theoryState_1316_, 2);
lean_dec(v_unused_1355_);
v___x_1330_ = v_theoryState_1316_;
v_isShared_1331_ = v_isSharedCheck_1354_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_satSolver_1328_);
lean_inc(v_bitvecState_1327_);
lean_inc(v_funState_1326_);
lean_dec(v_theoryState_1316_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1354_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 2, v_caches_1313_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_funState_1326_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_bitvecState_1327_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_caches_1313_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_satSolver_1328_);
v___x_1333_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 3, v___x_1333_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_satExpr_1317_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_hypQueue_1318_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_usedHyps_1319_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_solverTimeBudgetMs_1321_);
lean_ctor_set(v_reuseFailAlloc_1352_, 5, v_roundBudget_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, sizeof(void*)*6, v_didChange_1320_);
v___x_1335_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; size_t v_sz_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_st_ref_put(v_a_706_, v___x_1335_);
v_sz_1337_ = lean_array_size(v_hypotheses_1314_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1314_, v_sz_1337_, v___x_1306_, v___x_1234_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v_hypotheses_1314_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = lean_array_get_size(v_a_1339_);
v___x_1341_ = lean_nat_dec_eq(v___x_1340_, v___x_1233_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v_satExpr_1343_; uint8_t v___x_1344_; 
v___x_1342_ = lean_st_ref_get(v_a_706_);
v_satExpr_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_ref(v_satExpr_1343_);
lean_dec(v___x_1342_);
v___x_1344_ = lean_nat_dec_lt(v___x_1233_, v___x_1340_);
if (v___x_1344_ == 0)
{
lean_dec(v_a_1339_);
v___y_1031_ = v___x_1221_;
v___y_1032_ = v_a_1064_;
v_a_1033_ = v_satExpr_1343_;
goto v___jp_1030_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
if (v___x_1345_ == 0)
{
if (v___x_1344_ == 0)
{
lean_dec(v_a_1339_);
v___y_1031_ = v___x_1221_;
v___y_1032_ = v_a_1064_;
v_a_1033_ = v_satExpr_1343_;
goto v___jp_1030_;
}
else
{
size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_usize_of_nat(v___x_1340_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1339_, v___x_1306_, v___x_1346_, v_satExpr_1343_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1339_);
v___y_1057_ = v___x_1221_;
v___y_1058_ = v_a_1064_;
v___y_1059_ = v___x_1347_;
goto v___jp_1056_;
}
}
else
{
size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_usize_of_nat(v___x_1340_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1339_, v___x_1306_, v___x_1348_, v_satExpr_1343_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1339_);
v___y_1057_ = v___x_1221_;
v___y_1058_ = v_a_1064_;
v___y_1059_ = v___x_1349_;
goto v___jp_1056_;
}
}
}
else
{
uint8_t v___x_1350_; 
lean_dec(v_a_1339_);
v___x_1350_ = 2;
v___y_1025_ = v___x_1221_;
v___y_1026_ = v_a_1064_;
v_a_1027_ = v___x_1350_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1351_; 
v_a_1351_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1338_, 1);
v___y_1052_ = v___x_1221_;
v___y_1053_ = v_a_1064_;
v_a_1054_ = v_a_1351_;
goto v___jp_1051_;
}
}
}
}
}
}
else
{
uint8_t v___x_1357_; 
lean_dec(v___x_1311_);
v___x_1357_ = 0;
v___y_1025_ = v___x_1221_;
v___y_1026_ = v_a_1064_;
v_a_1027_ = v___x_1357_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_a_1358_; 
lean_dec(v___x_1293_);
v_a_1358_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1309_, 1);
v___y_1052_ = v___x_1221_;
v___y_1053_ = v_a_1064_;
v_a_1054_ = v_a_1358_;
goto v___jp_1051_;
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
uint8_t v___x_1369_; 
lean_dec_ref(v_hypQueue_1224_);
lean_del_object(v___x_1066_);
v___x_1369_ = 2;
v___y_1025_ = v___x_1221_;
v___y_1026_ = v_a_1064_;
v_a_1027_ = v___x_1369_;
goto v___jp_1024_;
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
if (lean_obj_tag(v___y_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___y_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___y_744_, 1);
v___y_721_ = v___y_743_;
v_a_722_ = v_a_745_;
goto v___jp_720_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___y_744_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___y_744_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___y_744_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___y_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
v___jp_754_:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_array_get_size(v_hypQueue_755_);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_nat_dec_eq(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v_goal_773_; lean_object* v_tacticContext_774_; lean_object* v___x_775_; lean_object* v_config_776_; lean_object* v_mode_777_; lean_object* v_timeout_778_; uint8_t v_trimProofs_779_; uint8_t v_binaryProofs_780_; uint8_t v_acNf_781_; uint8_t v_andFlattening_782_; uint8_t v_embeddedConstraintSubst_783_; uint8_t v_graphviz_784_; lean_object* v_maxSteps_785_; uint8_t v_solverMode_786_; uint8_t v_uf_787_; lean_object* v_cegarRounds_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_928_; 
v_goal_773_ = lean_ctor_get(v___y_756_, 0);
v_tacticContext_774_ = lean_ctor_get(v___y_756_, 2);
lean_inc_ref(v_tacticContext_774_);
v___x_775_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_774_);
v_config_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_ref(v_config_776_);
v_mode_777_ = lean_ctor_get(v___x_775_, 1);
lean_inc(v_mode_777_);
lean_dec_ref(v___x_775_);
v_timeout_778_ = lean_ctor_get(v_config_776_, 0);
v_trimProofs_779_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3);
v_binaryProofs_780_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 1);
v_acNf_781_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 2);
v_andFlattening_782_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_783_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 4);
v_graphviz_784_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 8);
v_maxSteps_785_ = lean_ctor_get(v_config_776_, 1);
v_solverMode_786_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 10);
v_uf_787_ = lean_ctor_get_uint8(v_config_776_, sizeof(void*)*3 + 11);
v_cegarRounds_788_ = lean_ctor_get(v_config_776_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v_config_776_);
if (v_isSharedCheck_928_ == 0)
{
v___x_790_ = v_config_776_;
v_isShared_791_ = v_isSharedCheck_928_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_cegarRounds_788_);
lean_inc(v_maxSteps_785_);
lean_inc(v_timeout_778_);
lean_dec(v_config_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_928_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_inc(v_goal_773_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_goal_773_);
if (v_isShared_791_ == 0)
{
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_timeout_778_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_maxSteps_785_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_cegarRounds_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3, v_trimProofs_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 1, v_binaryProofs_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 2, v_acNf_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 3, v_andFlattening_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 8, v_graphviz_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 10, v_solverMode_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*3 + 11, v_uf_787_);
v___x_794_ = v_reuseFailAlloc_927_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_theoryState_798_; lean_object* v_satExpr_799_; lean_object* v_hypQueue_800_; lean_object* v_usedHyps_801_; uint8_t v_didChange_802_; lean_object* v_solverTimeBudgetMs_803_; lean_object* v_roundBudget_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_926_; 
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*3 + 5, v___x_772_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*3 + 6, v___x_772_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*3 + 7, v___x_772_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*3 + 9, v___x_772_);
v___x_795_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_796_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_777_, v___x_794_, v___x_795_);
v___x_797_ = lean_st_ref_take(v___y_757_);
v_theoryState_798_ = lean_ctor_get(v___x_797_, 3);
v_satExpr_799_ = lean_ctor_get(v___x_797_, 0);
v_hypQueue_800_ = lean_ctor_get(v___x_797_, 1);
v_usedHyps_801_ = lean_ctor_get(v___x_797_, 2);
v_didChange_802_ = lean_ctor_get_uint8(v___x_797_, sizeof(void*)*6);
v_solverTimeBudgetMs_803_ = lean_ctor_get(v___x_797_, 4);
v_roundBudget_804_ = lean_ctor_get(v___x_797_, 5);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_926_ == 0)
{
v___x_806_ = v___x_797_;
v_isShared_807_ = v_isSharedCheck_926_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_roundBudget_804_);
lean_inc(v_solverTimeBudgetMs_803_);
lean_inc(v_theoryState_798_);
lean_inc(v_usedHyps_801_);
lean_inc(v_hypQueue_800_);
lean_inc(v_satExpr_799_);
lean_dec(v___x_797_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_926_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_funState_808_; lean_object* v_bitvecState_809_; lean_object* v_preprocessCaches_810_; lean_object* v_satSolver_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_925_; 
v_funState_808_ = lean_ctor_get(v_theoryState_798_, 0);
v_bitvecState_809_ = lean_ctor_get(v_theoryState_798_, 1);
v_preprocessCaches_810_ = lean_ctor_get(v_theoryState_798_, 2);
v_satSolver_811_ = lean_ctor_get(v_theoryState_798_, 3);
v_isSharedCheck_925_ = !lean_is_exclusive(v_theoryState_798_);
if (v_isSharedCheck_925_ == 0)
{
v___x_813_ = v_theoryState_798_;
v_isShared_814_ = v_isSharedCheck_925_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_satSolver_811_);
lean_inc(v_preprocessCaches_810_);
lean_inc(v_bitvecState_809_);
lean_inc(v_funState_808_);
lean_dec(v_theoryState_798_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_925_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 2, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_funState_808_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_bitvecState_809_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_satSolver_811_);
v___x_817_ = v_reuseFailAlloc_924_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 3, v___x_817_);
v___x_819_ = v___x_806_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_satExpr_799_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_hypQueue_800_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_usedHyps_801_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_solverTimeBudgetMs_803_);
lean_ctor_set(v_reuseFailAlloc_923_, 5, v_roundBudget_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*6, v_didChange_802_);
v___x_819_ = v_reuseFailAlloc_923_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_typeAnalysis_826_; lean_object* v_target_827_; lean_object* v_hypotheses_828_; uint8_t v_didChange_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_921_; 
v___x_820_ = lean_st_ref_put(v___y_757_, v___x_819_);
v___x_821_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_822_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7));
v___x_823_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_823_, 0, v___x_815_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_792_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*4, v___x_772_);
v___x_824_ = lean_st_mk_ref(v___x_823_);
v___x_825_ = lean_st_ref_take(v___x_824_);
v_typeAnalysis_826_ = lean_ctor_get(v___x_825_, 1);
v_target_827_ = lean_ctor_get(v___x_825_, 2);
v_hypotheses_828_ = lean_ctor_get(v___x_825_, 3);
v_didChange_829_ = lean_ctor_get_uint8(v___x_825_, sizeof(void*)*4);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_825_, 0);
lean_dec(v_unused_922_);
v___x_831_ = v___x_825_;
v_isShared_832_ = v_isSharedCheck_921_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_hypotheses_828_);
lean_inc(v_target_827_);
lean_inc(v_typeAnalysis_826_);
lean_dec(v___x_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_921_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_preprocessCaches_810_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_preprocessCaches_810_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_typeAnalysis_826_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_target_827_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_hypotheses_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*4, v_didChange_829_);
v___x_834_ = v_reuseFailAlloc_920_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; size_t v_sz_836_; size_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_835_ = lean_st_ref_put(v___x_824_, v___x_834_);
v_sz_836_ = lean_array_size(v_hypQueue_755_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_836_, v___x_837_, v_hypQueue_755_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_839_, v___x_796_, v___x_824_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec_ref(v___x_796_);
lean_dec_ref_known(v___x_839_, 1);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_911_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_911_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_911_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_911_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_st_ref_get(v___x_824_);
lean_dec(v___x_824_);
v___x_846_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_846_ == 0)
{
lean_object* v_caches_847_; lean_object* v_hypotheses_848_; lean_object* v___x_849_; lean_object* v_theoryState_850_; lean_object* v_satExpr_851_; lean_object* v_hypQueue_852_; lean_object* v_usedHyps_853_; uint8_t v_didChange_854_; lean_object* v_solverTimeBudgetMs_855_; lean_object* v_roundBudget_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_843_);
v_caches_847_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_caches_847_);
v_hypotheses_848_ = lean_ctor_get(v___x_845_, 3);
lean_inc_ref(v_hypotheses_848_);
lean_dec(v___x_845_);
v___x_849_ = lean_st_ref_take(v___y_757_);
v_theoryState_850_ = lean_ctor_get(v___x_849_, 3);
v_satExpr_851_ = lean_ctor_get(v___x_849_, 0);
v_hypQueue_852_ = lean_ctor_get(v___x_849_, 1);
v_usedHyps_853_ = lean_ctor_get(v___x_849_, 2);
v_didChange_854_ = lean_ctor_get_uint8(v___x_849_, sizeof(void*)*6);
v_solverTimeBudgetMs_855_ = lean_ctor_get(v___x_849_, 4);
v_roundBudget_856_ = lean_ctor_get(v___x_849_, 5);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_905_ == 0)
{
v___x_858_ = v___x_849_;
v_isShared_859_ = v_isSharedCheck_905_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_roundBudget_856_);
lean_inc(v_solverTimeBudgetMs_855_);
lean_inc(v_theoryState_850_);
lean_inc(v_usedHyps_853_);
lean_inc(v_hypQueue_852_);
lean_inc(v_satExpr_851_);
lean_dec(v___x_849_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_905_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_funState_860_; lean_object* v_bitvecState_861_; lean_object* v_satSolver_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_903_; 
v_funState_860_ = lean_ctor_get(v_theoryState_850_, 0);
v_bitvecState_861_ = lean_ctor_get(v_theoryState_850_, 1);
v_satSolver_862_ = lean_ctor_get(v_theoryState_850_, 3);
v_isSharedCheck_903_ = !lean_is_exclusive(v_theoryState_850_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_theoryState_850_, 2);
lean_dec(v_unused_904_);
v___x_864_ = v_theoryState_850_;
v_isShared_865_ = v_isSharedCheck_903_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_satSolver_862_);
lean_inc(v_bitvecState_861_);
lean_inc(v_funState_860_);
lean_dec(v_theoryState_850_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_903_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 2, v_caches_847_);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_funState_860_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_bitvecState_861_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_caches_847_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_satSolver_862_);
v___x_867_ = v_reuseFailAlloc_902_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 3, v___x_867_);
v___x_869_ = v___x_858_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_satExpr_851_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_hypQueue_852_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_usedHyps_853_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_solverTimeBudgetMs_855_);
lean_ctor_set(v_reuseFailAlloc_901_, 5, v_roundBudget_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*6, v_didChange_854_);
v___x_869_ = v_reuseFailAlloc_901_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; size_t v_sz_871_; lean_object* v___x_872_; 
v___x_870_ = lean_st_ref_put(v___y_757_, v___x_869_);
v_sz_871_ = lean_array_size(v_hypotheses_848_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_848_, v_sz_871_, v___x_837_, v___x_822_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec_ref(v_hypotheses_848_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_892_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_892_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_892_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_892_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_array_get_size(v_a_873_);
v___x_878_ = lean_nat_dec_eq(v___x_877_, v___x_771_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v_satExpr_880_; uint8_t v___x_881_; 
lean_del_object(v___x_875_);
v___x_879_ = lean_st_ref_get(v___y_757_);
v_satExpr_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_satExpr_880_);
lean_dec(v___x_879_);
v___x_881_ = lean_nat_dec_lt(v___x_771_, v___x_877_);
if (v___x_881_ == 0)
{
lean_dec(v_a_873_);
v___y_721_ = v___y_757_;
v_a_722_ = v_satExpr_880_;
goto v___jp_720_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_le(v___x_877_, v___x_877_);
if (v___x_882_ == 0)
{
if (v___x_881_ == 0)
{
lean_dec(v_a_873_);
v___y_721_ = v___y_757_;
v_a_722_ = v_satExpr_880_;
goto v___jp_720_;
}
else
{
size_t v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_usize_of_nat(v___x_877_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_873_, v___x_837_, v___x_883_, v_satExpr_880_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v_a_873_);
v___y_743_ = v___y_757_;
v___y_744_ = v___x_884_;
goto v___jp_742_;
}
}
else
{
size_t v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_usize_of_nat(v___x_877_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_873_, v___x_837_, v___x_885_, v_satExpr_880_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v_a_873_);
v___y_743_ = v___y_757_;
v___y_744_ = v___x_886_;
goto v___jp_742_;
}
}
}
else
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec(v_a_873_);
v___x_887_ = 2;
v___x_888_ = lean_box(v___x_887_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_888_);
v___x_890_ = v___x_875_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_872_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_872_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
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
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v___x_845_);
v___x_906_ = 0;
v___x_907_ = lean_box(v___x_906_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_907_);
v___x_909_ = v___x_843_;
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
lean_dec(v___x_824_);
v_a_912_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_840_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_840_);
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
}
}
}
}
else
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_hypQueue_755_);
v___x_929_ = 2;
v___x_930_ = lean_box(v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1409_, lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1410_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1427_ = _args[0];
lean_object* v_msg_1428_ = _args[1];
lean_object* v___y_1429_ = _args[2];
lean_object* v___y_1430_ = _args[3];
lean_object* v___y_1431_ = _args[4];
lean_object* v___y_1432_ = _args[5];
lean_object* v___y_1433_ = _args[6];
lean_object* v___y_1434_ = _args[7];
lean_object* v___y_1435_ = _args[8];
lean_object* v___y_1436_ = _args[9];
lean_object* v___y_1437_ = _args[10];
lean_object* v___y_1438_ = _args[11];
lean_object* v___y_1439_ = _args[12];
lean_object* v___y_1440_ = _args[13];
lean_object* v___y_1441_ = _args[14];
lean_object* v___y_1442_ = _args[15];
lean_object* v___y_1443_ = _args[16];
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1427_, v_msg_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_1445_, v_i_1446_, v_stop_1447_, v_b_1448_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object** _args){
lean_object* v_as_1465_ = _args[0];
lean_object* v_i_1466_ = _args[1];
lean_object* v_stop_1467_ = _args[2];
lean_object* v_b_1468_ = _args[3];
lean_object* v___y_1469_ = _args[4];
lean_object* v___y_1470_ = _args[5];
lean_object* v___y_1471_ = _args[6];
lean_object* v___y_1472_ = _args[7];
lean_object* v___y_1473_ = _args[8];
lean_object* v___y_1474_ = _args[9];
lean_object* v___y_1475_ = _args[10];
lean_object* v___y_1476_ = _args[11];
lean_object* v___y_1477_ = _args[12];
lean_object* v___y_1478_ = _args[13];
lean_object* v___y_1479_ = _args[14];
lean_object* v___y_1480_ = _args[15];
lean_object* v___y_1481_ = _args[16];
lean_object* v___y_1482_ = _args[17];
lean_object* v___y_1483_ = _args[18];
_start:
{
size_t v_i_boxed_1484_; size_t v_stop_boxed_1485_; lean_object* v_res_1486_; 
v_i_boxed_1484_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_stop_boxed_1485_ = lean_unbox_usize(v_stop_1467_);
lean_dec(v_stop_1467_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1465_, v_i_boxed_1484_, v_stop_boxed_1485_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v_as_1465_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object* v_00_u03b1_1487_, lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_1488_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1505_ = _args[0];
lean_object* v_x_1506_ = _args[1];
lean_object* v___y_1507_ = _args[2];
lean_object* v___y_1508_ = _args[3];
lean_object* v___y_1509_ = _args[4];
lean_object* v___y_1510_ = _args[5];
lean_object* v___y_1511_ = _args[6];
lean_object* v___y_1512_ = _args[7];
lean_object* v___y_1513_ = _args[8];
lean_object* v___y_1514_ = _args[9];
lean_object* v___y_1515_ = _args[10];
lean_object* v___y_1516_ = _args[11];
lean_object* v___y_1517_ = _args[12];
lean_object* v___y_1518_ = _args[13];
lean_object* v___y_1519_ = _args[14];
lean_object* v___y_1520_ = _args[15];
lean_object* v___y_1521_ = _args[16];
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(v_00_u03b1_1505_, v_x_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object* v_oldTraces_1523_, lean_object* v_data_1524_, lean_object* v_ref_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_1523_, v_data_1524_, v_ref_1525_, v_msg_1526_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object** _args){
lean_object* v_oldTraces_1543_ = _args[0];
lean_object* v_data_1544_ = _args[1];
lean_object* v_ref_1545_ = _args[2];
lean_object* v_msg_1546_ = _args[3];
lean_object* v___y_1547_ = _args[4];
lean_object* v___y_1548_ = _args[5];
lean_object* v___y_1549_ = _args[6];
lean_object* v___y_1550_ = _args[7];
lean_object* v___y_1551_ = _args[8];
lean_object* v___y_1552_ = _args[9];
lean_object* v___y_1553_ = _args[10];
lean_object* v___y_1554_ = _args[11];
lean_object* v___y_1555_ = _args[12];
lean_object* v___y_1556_ = _args[13];
lean_object* v___y_1557_ = _args[14];
lean_object* v___y_1558_ = _args[15];
lean_object* v___y_1559_ = _args[16];
lean_object* v___y_1560_ = _args[17];
lean_object* v___y_1561_ = _args[18];
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1543_, v_data_1544_, v_ref_1545_, v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1562_;
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

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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx(v_x_boxed_6_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(lean_object* v_solved_23_){
_start:
{
lean_inc(v_solved_23_);
return v_solved_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg___boxed(lean_object* v_solved_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(v_solved_24_);
lean_dec(v_solved_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_solved_29_){
_start:
{
lean_inc(v_solved_29_);
return v_solved_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_solved_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_solved_33_);
lean_dec(v_solved_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(lean_object* v_newHyps_36_){
_start:
{
lean_inc(v_newHyps_36_);
return v_newHyps_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg___boxed(lean_object* v_newHyps_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(v_newHyps_37_);
lean_dec(v_newHyps_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_newHyps_42_){
_start:
{
lean_inc(v_newHyps_42_);
return v_newHyps_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_newHyps_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_newHyps_46_);
lean_dec(v_newHyps_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(lean_object* v_none_49_){
_start:
{
lean_inc(v_none_49_);
return v_none_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg___boxed(lean_object* v_none_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(v_none_50_);
lean_dec(v_none_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_none_55_){
_start:
{
lean_inc(v_none_55_);
return v_none_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_none_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_none_59_);
lean_dec(v_none_59_);
return v_res_61_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(32u);
v___x_63_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_65_ = ((size_t)5ULL);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_unsigned_to_nat(32u);
v___x_68_ = lean_mk_empty_array_with_capacity(v___x_67_);
v___x_69_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0);
v___x_70_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_66_);
lean_ctor_set(v___x_70_, 3, v___x_66_);
lean_ctor_set_usize(v___x_70_, 4, v___x_65_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_traceState_74_; lean_object* v_traces_75_; lean_object* v___x_76_; lean_object* v_traceState_77_; lean_object* v_env_78_; lean_object* v_nextMacroScope_79_; lean_object* v_ngen_80_; lean_object* v_auxDeclNGen_81_; lean_object* v_cache_82_; lean_object* v_recordedDeps_83_; lean_object* v_messages_84_; lean_object* v_infoState_85_; lean_object* v_snapshotTasks_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_105_; 
v___x_73_ = lean_st_ref_get(v___y_71_);
v_traceState_74_ = lean_ctor_get(v___x_73_, 4);
lean_inc_ref(v_traceState_74_);
lean_dec(v___x_73_);
v_traces_75_ = lean_ctor_get(v_traceState_74_, 0);
lean_inc_ref(v_traces_75_);
lean_dec_ref(v_traceState_74_);
v___x_76_ = lean_st_ref_take(v___y_71_);
v_traceState_77_ = lean_ctor_get(v___x_76_, 4);
v_env_78_ = lean_ctor_get(v___x_76_, 0);
v_nextMacroScope_79_ = lean_ctor_get(v___x_76_, 1);
v_ngen_80_ = lean_ctor_get(v___x_76_, 2);
v_auxDeclNGen_81_ = lean_ctor_get(v___x_76_, 3);
v_cache_82_ = lean_ctor_get(v___x_76_, 5);
v_recordedDeps_83_ = lean_ctor_get(v___x_76_, 6);
v_messages_84_ = lean_ctor_get(v___x_76_, 7);
v_infoState_85_ = lean_ctor_get(v___x_76_, 8);
v_snapshotTasks_86_ = lean_ctor_get(v___x_76_, 9);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_105_ == 0)
{
v___x_88_ = v___x_76_;
v_isShared_89_ = v_isSharedCheck_105_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_snapshotTasks_86_);
lean_inc(v_infoState_85_);
lean_inc(v_messages_84_);
lean_inc(v_recordedDeps_83_);
lean_inc(v_cache_82_);
lean_inc(v_traceState_77_);
lean_inc(v_auxDeclNGen_81_);
lean_inc(v_ngen_80_);
lean_inc(v_nextMacroScope_79_);
lean_inc(v_env_78_);
lean_dec(v___x_76_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_105_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint64_t v_tid_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_103_; 
v_tid_90_ = lean_ctor_get_uint64(v_traceState_77_, sizeof(void*)*1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_traceState_77_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v_traceState_77_, 0);
lean_dec(v_unused_104_);
v___x_92_ = v_traceState_77_;
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
else
{
lean_dec(v_traceState_77_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_103_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_94_);
v___x_96_ = v___x_92_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_94_);
lean_ctor_set_uint64(v_reuseFailAlloc_102_, sizeof(void*)*1, v_tid_90_);
v___x_96_ = v_reuseFailAlloc_102_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_96_);
v___x_98_ = v___x_88_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_env_78_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_nextMacroScope_79_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_ngen_80_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_auxDeclNGen_81_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_101_, 5, v_cache_82_);
lean_ctor_set(v_reuseFailAlloc_101_, 6, v_recordedDeps_83_);
lean_ctor_set(v_reuseFailAlloc_101_, 7, v_messages_84_);
lean_ctor_set(v_reuseFailAlloc_101_, 8, v_infoState_85_);
lean_ctor_set(v_reuseFailAlloc_101_, 9, v_snapshotTasks_86_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_st_ref_put(v___y_71_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v_traces_75_);
return v___x_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___boxed(lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_106_);
lean_dec(v___y_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object* v_opts_141_, lean_object* v_opt_142_){
_start:
{
lean_object* v_name_143_; lean_object* v_defValue_144_; lean_object* v_map_145_; lean_object* v___x_146_; 
v_name_143_ = lean_ctor_get(v_opt_142_, 0);
v_defValue_144_ = lean_ctor_get(v_opt_142_, 1);
v_map_145_ = lean_ctor_get(v_opts_141_, 0);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_145_, v_name_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = lean_unbox(v_defValue_144_);
return v___x_147_;
}
else
{
lean_object* v_val_148_; 
v_val_148_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_146_, 1);
if (lean_obj_tag(v_val_148_) == 1)
{
uint8_t v_v_149_; 
v_v_149_ = lean_ctor_get_uint8(v_val_148_, 0);
lean_dec_ref_known(v_val_148_, 0);
return v_v_149_;
}
else
{
uint8_t v___x_150_; 
lean_dec(v_val_148_);
v___x_150_ = lean_unbox(v_defValue_144_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object* v_opts_151_, lean_object* v_opt_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_151_, v_opt_152_);
lean_dec_ref(v_opt_152_);
lean_dec_ref(v_opts_151_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0));
v___x_157_ = l_Lean_stringToMessageData(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object* v_x_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object* v_x_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v_x_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v_x_176_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v_x_193_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v_x_193_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v_x_193_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v_x_193_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v_x_193_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v_x_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 0);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg___boxed(lean_object* v_x_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_211_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(lean_object* v_e_214_){
_start:
{
if (lean_obj_tag(v_e_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = 2;
return v___x_215_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9___boxed(lean_object* v_e_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_e_217_);
lean_dec_ref(v_e_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(lean_object* v_opts_220_, lean_object* v_opt_221_){
_start:
{
lean_object* v_name_222_; lean_object* v_defValue_223_; lean_object* v_map_224_; lean_object* v___x_225_; 
v_name_222_ = lean_ctor_get(v_opt_221_, 0);
v_defValue_223_ = lean_ctor_get(v_opt_221_, 1);
v_map_224_ = lean_ctor_get(v_opts_220_, 0);
v___x_225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_224_, v_name_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_inc(v_defValue_223_);
return v_defValue_223_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_225_, 1);
if (lean_obj_tag(v_val_226_) == 3)
{
lean_object* v_v_227_; 
v_v_227_ = lean_ctor_get(v_val_226_, 0);
lean_inc(v_v_227_);
lean_dec_ref_known(v_val_226_, 1);
return v_v_227_;
}
else
{
lean_dec(v_val_226_);
lean_inc(v_defValue_223_);
return v_defValue_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10___boxed(lean_object* v_opts_228_, lean_object* v_opt_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_228_, v_opt_229_);
lean_dec_ref(v_opt_229_);
lean_dec_ref(v_opts_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(size_t v_sz_231_, size_t v_i_232_, lean_object* v_bs_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_lt(v_i_232_, v_sz_231_);
if (v___x_234_ == 0)
{
return v_bs_233_;
}
else
{
lean_object* v_v_235_; lean_object* v_msg_236_; lean_object* v___x_237_; lean_object* v_bs_x27_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v_v_235_ = lean_array_uget_borrowed(v_bs_233_, v_i_232_);
v_msg_236_ = lean_ctor_get(v_v_235_, 1);
lean_inc_ref(v_msg_236_);
v___x_237_ = lean_unsigned_to_nat(0u);
v_bs_x27_238_ = lean_array_uset(v_bs_233_, v_i_232_, v___x_237_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_232_, v___x_239_);
v___x_241_ = lean_array_uset(v_bs_x27_238_, v_i_232_, v_msg_236_);
v_i_232_ = v___x_240_;
v_bs_233_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_bs_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_boxed_246_, v_i_boxed_247_, v_bs_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v___x_257_; lean_object* v_toCold_258_; lean_object* v_mctx_259_; lean_object* v_lctx_260_; lean_object* v_options_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_255_);
v___x_257_ = lean_st_ref_get(v___y_251_);
v_toCold_258_ = lean_ctor_get(v___y_252_, 0);
v_mctx_259_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_mctx_259_);
lean_dec(v___x_257_);
v_lctx_260_ = lean_ctor_get(v___y_250_, 2);
v_options_261_ = lean_ctor_get(v_toCold_258_, 2);
lean_inc_ref(v_options_261_);
lean_inc_ref(v_lctx_260_);
v___x_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_262_, 0, v_env_256_);
lean_ctor_set(v___x_262_, 1, v_mctx_259_);
lean_ctor_set(v___x_262_, 2, v_lctx_260_);
lean_ctor_set(v___x_262_, 3, v_options_261_);
v___x_263_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_msgData_249_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object* v_msgData_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msgData_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(lean_object* v_oldTraces_272_, lean_object* v_data_273_, lean_object* v_ref_274_, lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_toCold_281_; lean_object* v_currRecDepth_282_; lean_object* v_ref_283_; uint16_t v_optionFlags_284_; uint8_t v_suppressElabErrors_285_; uint8_t v_isRecordingDeps_286_; lean_object* v_ref_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_traceState_290_; lean_object* v_traces_291_; lean_object* v___x_292_; size_t v_sz_293_; size_t v___x_294_; lean_object* v___x_295_; lean_object* v_msg_296_; lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_336_; 
v_toCold_281_ = lean_ctor_get(v___y_278_, 0);
v_currRecDepth_282_ = lean_ctor_get(v___y_278_, 1);
v_ref_283_ = lean_ctor_get(v___y_278_, 2);
v_optionFlags_284_ = lean_ctor_get_uint16(v___y_278_, sizeof(void*)*3);
v_suppressElabErrors_285_ = lean_ctor_get_uint8(v___y_278_, sizeof(void*)*3 + 2);
v_isRecordingDeps_286_ = lean_ctor_get_uint8(v___y_278_, sizeof(void*)*3 + 3);
v_ref_287_ = l_Lean_replaceRef(v_ref_274_, v_ref_283_);
lean_inc(v_currRecDepth_282_);
lean_inc_ref(v_toCold_281_);
v___x_288_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_288_, 0, v_toCold_281_);
lean_ctor_set(v___x_288_, 1, v_currRecDepth_282_);
lean_ctor_set(v___x_288_, 2, v_ref_287_);
lean_ctor_set_uint16(v___x_288_, sizeof(void*)*3, v_optionFlags_284_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*3 + 2, v_suppressElabErrors_285_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*3 + 3, v_isRecordingDeps_286_);
v___x_289_ = lean_st_ref_get(v___y_279_);
v_traceState_290_ = lean_ctor_get(v___x_289_, 4);
lean_inc_ref(v_traceState_290_);
lean_dec(v___x_289_);
v_traces_291_ = lean_ctor_get(v_traceState_290_, 0);
lean_inc_ref(v_traces_291_);
lean_dec_ref(v_traceState_290_);
v___x_292_ = l_Lean_PersistentArray_toArray___redArg(v_traces_291_);
lean_dec_ref(v_traces_291_);
v_sz_293_ = lean_array_size(v___x_292_);
v___x_294_ = ((size_t)0ULL);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_293_, v___x_294_, v___x_292_);
v_msg_296_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_296_, 0, v_data_273_);
lean_ctor_set(v_msg_296_, 1, v_msg_275_);
lean_ctor_set(v_msg_296_, 2, v___x_295_);
v___x_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_296_, v___y_276_, v___y_277_, v___x_288_, v___y_279_);
lean_dec_ref_known(v___x_288_, 3);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_336_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_336_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_336_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_recordedDeps_309_; lean_object* v_messages_310_; lean_object* v_infoState_311_; lean_object* v_snapshotTasks_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_335_; 
v___x_302_ = lean_st_ref_take(v___y_279_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
v_env_304_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_305_ = lean_ctor_get(v___x_302_, 1);
v_ngen_306_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_307_ = lean_ctor_get(v___x_302_, 3);
v_cache_308_ = lean_ctor_get(v___x_302_, 5);
v_recordedDeps_309_ = lean_ctor_get(v___x_302_, 6);
v_messages_310_ = lean_ctor_get(v___x_302_, 7);
v_infoState_311_ = lean_ctor_get(v___x_302_, 8);
v_snapshotTasks_312_ = lean_ctor_get(v___x_302_, 9);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_335_ == 0)
{
v___x_314_ = v___x_302_;
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_snapshotTasks_312_);
lean_inc(v_infoState_311_);
lean_inc(v_messages_310_);
lean_inc(v_recordedDeps_309_);
lean_inc(v_cache_308_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_307_);
lean_inc(v_ngen_306_);
lean_inc(v_nextMacroScope_305_);
lean_inc(v_env_304_);
lean_dec(v___x_302_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint64_t v_tid_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_333_; 
v_tid_316_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_traceState_303_, 0);
lean_dec(v_unused_334_);
v___x_318_ = v_traceState_303_;
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_traceState_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_320_ = lean_box(0);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_ref_274_);
lean_ctor_set(v___x_321_, 1, v_a_298_);
v___x_322_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_272_, v___x_321_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_322_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_322_);
lean_ctor_set_uint64(v_reuseFailAlloc_332_, sizeof(void*)*1, v_tid_316_);
v___x_324_ = v_reuseFailAlloc_332_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_324_);
v___x_326_ = v___x_314_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_recordedDeps_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_messages_310_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_infoState_311_);
lean_ctor_set(v_reuseFailAlloc_331_, 9, v_snapshotTasks_312_);
v___x_326_ = v_reuseFailAlloc_331_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_st_ref_put(v___y_279_, v___x_326_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_320_);
v___x_329_ = v___x_300_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_320_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_337_, lean_object* v_data_338_, lean_object* v_ref_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_337_, v_data_338_, v_ref_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0(void){
_start:
{
lean_object* v___x_347_; double v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_float_of_nat(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3(void){
_start:
{
lean_object* v___x_352_; double v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1000u);
v___x_353_ = lean_float_of_nat(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object* v_cls_354_, uint8_t v_collapsed_355_, lean_object* v_tag_356_, lean_object* v_opts_357_, uint8_t v_clsEnabled_358_, lean_object* v_oldTraces_359_, lean_object* v_msg_360_, lean_object* v_resStartStop_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v_data_382_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___y_398_; lean_object* v_a_399_; uint8_t v___y_414_; double v___y_446_; 
v_fst_377_ = lean_ctor_get(v_resStartStop_361_, 0);
lean_inc(v_fst_377_);
v_snd_378_ = lean_ctor_get(v_resStartStop_361_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v_resStartStop_361_);
v_fst_393_ = lean_ctor_get(v_snd_378_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v_snd_378_, 1);
lean_inc(v_snd_394_);
lean_dec(v_snd_378_);
v___x_395_ = l_Lean_trace_profiler;
v___x_396_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_357_, v___x_395_);
if (v___x_396_ == 0)
{
v___y_414_ = v___x_396_;
goto v___jp_413_;
}
else
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = l_Lean_trace_profiler_useHeartbeats;
v___x_452_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_357_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; double v___x_455_; double v___x_456_; double v___x_457_; 
v___x_453_ = l_Lean_trace_profiler_threshold;
v___x_454_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_357_, v___x_453_);
v___x_455_ = lean_float_of_nat(v___x_454_);
v___x_456_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3);
v___x_457_ = lean_float_div(v___x_455_, v___x_456_);
v___y_446_ = v___x_457_;
goto v___jp_445_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; double v___x_460_; 
v___x_458_ = l_Lean_trace_profiler_threshold;
v___x_459_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_357_, v___x_458_);
v___x_460_ = lean_float_of_nat(v___x_459_);
v___y_446_ = v___x_460_;
goto v___jp_445_;
}
}
v___jp_379_:
{
lean_object* v___x_383_; 
lean_inc(v___y_381_);
v___x_383_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_359_, v_data_382_, v___y_381_, v___y_380_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; 
lean_dec_ref_known(v___x_383_, 1);
v___x_384_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_377_);
return v___x_384_;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_fst_377_);
v_a_385_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_383_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
v___jp_397_:
{
uint8_t v_result_400_; lean_object* v___x_401_; lean_object* v___x_402_; double v___x_403_; lean_object* v_data_404_; 
v_result_400_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_fst_377_);
v___x_401_ = lean_box(v_result_400_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0);
lean_inc_ref(v_tag_356_);
lean_inc_ref(v___x_402_);
lean_inc(v_cls_354_);
v_data_404_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_404_, 0, v_cls_354_);
lean_ctor_set(v_data_404_, 1, v___x_402_);
lean_ctor_set(v_data_404_, 2, v_tag_356_);
lean_ctor_set_float(v_data_404_, sizeof(void*)*3, v___x_403_);
lean_ctor_set_float(v_data_404_, sizeof(void*)*3 + 8, v___x_403_);
lean_ctor_set_uint8(v_data_404_, sizeof(void*)*3 + 16, v_collapsed_355_);
if (v___x_396_ == 0)
{
lean_dec_ref_known(v___x_402_, 1);
lean_dec(v_snd_394_);
lean_dec(v_fst_393_);
lean_dec_ref(v_tag_356_);
lean_dec(v_cls_354_);
v___y_380_ = v_a_399_;
v___y_381_ = v___y_398_;
v_data_382_ = v_data_404_;
goto v___jp_379_;
}
else
{
lean_object* v_data_405_; double v___x_406_; double v___x_407_; 
lean_dec_ref_known(v_data_404_, 3);
v_data_405_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_405_, 0, v_cls_354_);
lean_ctor_set(v_data_405_, 1, v___x_402_);
lean_ctor_set(v_data_405_, 2, v_tag_356_);
v___x_406_ = lean_unbox_float(v_fst_393_);
lean_dec(v_fst_393_);
lean_ctor_set_float(v_data_405_, sizeof(void*)*3, v___x_406_);
v___x_407_ = lean_unbox_float(v_snd_394_);
lean_dec(v_snd_394_);
lean_ctor_set_float(v_data_405_, sizeof(void*)*3 + 8, v___x_407_);
lean_ctor_set_uint8(v_data_405_, sizeof(void*)*3 + 16, v_collapsed_355_);
v___y_380_ = v_a_399_;
v___y_381_ = v___y_398_;
v_data_382_ = v_data_405_;
goto v___jp_379_;
}
}
v___jp_408_:
{
lean_object* v_ref_409_; lean_object* v___x_410_; 
v_ref_409_ = lean_ctor_get(v___y_374_, 2);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
lean_inc(v___y_369_);
lean_inc_ref(v___y_368_);
lean_inc(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v_fst_377_);
v___x_410_ = lean_apply_16(v_msg_360_, v_fst_377_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, lean_box(0));
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___y_398_ = v_ref_409_;
v_a_399_ = v_a_411_;
goto v___jp_397_;
}
else
{
lean_object* v___x_412_; 
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2);
v___y_398_ = v_ref_409_;
v_a_399_ = v___x_412_;
goto v___jp_397_;
}
}
v___jp_413_:
{
if (v_clsEnabled_358_ == 0)
{
if (v___y_414_ == 0)
{
lean_object* v___x_415_; lean_object* v_traceState_416_; lean_object* v_env_417_; lean_object* v_nextMacroScope_418_; lean_object* v_ngen_419_; lean_object* v_auxDeclNGen_420_; lean_object* v_cache_421_; lean_object* v_recordedDeps_422_; lean_object* v_messages_423_; lean_object* v_infoState_424_; lean_object* v_snapshotTasks_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_snd_394_);
lean_dec(v_fst_393_);
lean_dec_ref(v_msg_360_);
lean_dec_ref(v_tag_356_);
lean_dec(v_cls_354_);
v___x_415_ = lean_st_ref_take(v___y_375_);
v_traceState_416_ = lean_ctor_get(v___x_415_, 4);
v_env_417_ = lean_ctor_get(v___x_415_, 0);
v_nextMacroScope_418_ = lean_ctor_get(v___x_415_, 1);
v_ngen_419_ = lean_ctor_get(v___x_415_, 2);
v_auxDeclNGen_420_ = lean_ctor_get(v___x_415_, 3);
v_cache_421_ = lean_ctor_get(v___x_415_, 5);
v_recordedDeps_422_ = lean_ctor_get(v___x_415_, 6);
v_messages_423_ = lean_ctor_get(v___x_415_, 7);
v_infoState_424_ = lean_ctor_get(v___x_415_, 8);
v_snapshotTasks_425_ = lean_ctor_get(v___x_415_, 9);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_444_ == 0)
{
v___x_427_ = v___x_415_;
v_isShared_428_ = v_isSharedCheck_444_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snapshotTasks_425_);
lean_inc(v_infoState_424_);
lean_inc(v_messages_423_);
lean_inc(v_recordedDeps_422_);
lean_inc(v_cache_421_);
lean_inc(v_traceState_416_);
lean_inc(v_auxDeclNGen_420_);
lean_inc(v_ngen_419_);
lean_inc(v_nextMacroScope_418_);
lean_inc(v_env_417_);
lean_dec(v___x_415_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_444_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
uint64_t v_tid_429_; lean_object* v_traces_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_443_; 
v_tid_429_ = lean_ctor_get_uint64(v_traceState_416_, sizeof(void*)*1);
v_traces_430_ = lean_ctor_get(v_traceState_416_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_traceState_416_);
if (v_isSharedCheck_443_ == 0)
{
v___x_432_ = v_traceState_416_;
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_traces_430_);
lean_dec(v_traceState_416_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_359_, v_traces_430_);
lean_dec_ref(v_traces_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_434_);
lean_ctor_set_uint64(v_reuseFailAlloc_442_, sizeof(void*)*1, v_tid_429_);
v___x_436_ = v_reuseFailAlloc_442_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 4, v___x_436_);
v___x_438_ = v___x_427_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_env_417_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_nextMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_ngen_419_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_auxDeclNGen_420_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_cache_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 6, v_recordedDeps_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 7, v_messages_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 8, v_infoState_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 9, v_snapshotTasks_425_);
v___x_438_ = v_reuseFailAlloc_441_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_st_ref_put(v___y_375_, v___x_438_);
v___x_440_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_377_);
return v___x_440_;
}
}
}
}
}
else
{
goto v___jp_408_;
}
}
else
{
goto v___jp_408_;
}
}
v___jp_445_:
{
double v___x_447_; double v___x_448_; double v___x_449_; uint8_t v___x_450_; 
v___x_447_ = lean_unbox_float(v_snd_394_);
v___x_448_ = lean_unbox_float(v_fst_393_);
v___x_449_ = lean_float_sub(v___x_447_, v___x_448_);
v___x_450_ = lean_float_decLt(v___y_446_, v___x_449_);
v___y_414_ = v___x_450_;
goto v___jp_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object** _args){
lean_object* v_cls_461_ = _args[0];
lean_object* v_collapsed_462_ = _args[1];
lean_object* v_tag_463_ = _args[2];
lean_object* v_opts_464_ = _args[3];
lean_object* v_clsEnabled_465_ = _args[4];
lean_object* v_oldTraces_466_ = _args[5];
lean_object* v_msg_467_ = _args[6];
lean_object* v_resStartStop_468_ = _args[7];
lean_object* v___y_469_ = _args[8];
lean_object* v___y_470_ = _args[9];
lean_object* v___y_471_ = _args[10];
lean_object* v___y_472_ = _args[11];
lean_object* v___y_473_ = _args[12];
lean_object* v___y_474_ = _args[13];
lean_object* v___y_475_ = _args[14];
lean_object* v___y_476_ = _args[15];
lean_object* v___y_477_ = _args[16];
lean_object* v___y_478_ = _args[17];
lean_object* v___y_479_ = _args[18];
lean_object* v___y_480_ = _args[19];
lean_object* v___y_481_ = _args[20];
lean_object* v___y_482_ = _args[21];
lean_object* v___y_483_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_484_; uint8_t v_clsEnabled_boxed_485_; lean_object* v_res_486_; 
v_collapsed_boxed_484_ = lean_unbox(v_collapsed_462_);
v_clsEnabled_boxed_485_ = lean_unbox(v_clsEnabled_465_);
v_res_486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_cls_461_, v_collapsed_boxed_484_, v_tag_463_, v_opts_464_, v_clsEnabled_boxed_485_, v_oldTraces_466_, v_msg_467_, v_resStartStop_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v_opts_464_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(size_t v_sz_487_, size_t v_i_488_, lean_object* v_bs_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_488_, v_sz_487_);
if (v___x_490_ == 0)
{
return v_bs_489_;
}
else
{
lean_object* v_v_491_; lean_object* v_hyp_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_v_491_ = lean_array_uget_borrowed(v_bs_489_, v_i_488_);
v_hyp_492_ = lean_ctor_get(v_v_491_, 0);
lean_inc_ref(v_hyp_492_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_489_, v_i_488_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_488_, v___x_495_);
v___x_497_ = lean_array_uset(v_bs_x27_494_, v_i_488_, v_hyp_492_);
v_i_488_ = v___x_496_;
v_bs_489_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_503_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_boxed_502_, v_i_boxed_503_, v_bs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_ref_511_; lean_object* v___x_512_; lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_ref_511_ = lean_ctor_get(v___y_508_, 2);
v___x_512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_inc(v_ref_511_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_ref_511_);
lean_ctor_set(v___x_517_, 1, v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object* v_as_536_, size_t v_sz_537_, size_t v_i_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_a_556_; uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_b_539_);
return v___x_561_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_562_ = lean_array_uget_borrowed(v_as_536_, v_i_538_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0));
v___x_564_ = l_Lean_Core_checkSystem(v___x_563_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_type_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec_ref_known(v___x_564_, 1);
v_type_565_ = lean_ctor_get(v_a_562_, 1);
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2));
v___x_567_ = l_Lean_Expr_isConstOf(v_type_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v___y_542_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
lean_dec_ref_known(v___x_568_, 1);
lean_inc(v_a_562_);
v___x_569_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_a_562_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
if (lean_obj_tag(v_a_570_) == 1)
{
lean_object* v_val_571_; lean_object* v___x_572_; 
v_val_571_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v_a_570_, 1);
v___x_572_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v___y_542_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l_Array_append___redArg(v_b_539_, v_a_573_);
lean_dec(v_a_573_);
v___x_575_ = lean_array_push(v___x_574_, v_val_571_);
v_a_556_ = v___x_575_;
goto v___jp_555_;
}
else
{
lean_dec(v_val_571_);
lean_dec_ref(v_b_539_);
return v___x_572_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_a_570_);
v___x_576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4);
lean_inc_ref(v_type_565_);
v___x_577_ = l_Lean_MessageData_ofExpr(v_type_565_);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v___x_578_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_dec_ref_known(v___x_579_, 1);
v_a_556_ = v_b_539_;
goto v___jp_555_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_b_539_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_b_539_);
v_a_588_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_569_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_569_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_b_539_);
v_a_596_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_568_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_568_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
v_a_556_ = v_b_539_;
goto v___jp_555_;
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_b_539_);
v_a_604_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_564_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_564_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
v___jp_555_:
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_538_, v___x_557_);
v_i_538_ = v___x_558_;
v_b_539_ = v_a_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object** _args){
lean_object* v_as_612_ = _args[0];
lean_object* v_sz_613_ = _args[1];
lean_object* v_i_614_ = _args[2];
lean_object* v_b_615_ = _args[3];
lean_object* v___y_616_ = _args[4];
lean_object* v___y_617_ = _args[5];
lean_object* v___y_618_ = _args[6];
lean_object* v___y_619_ = _args[7];
lean_object* v___y_620_ = _args[8];
lean_object* v___y_621_ = _args[9];
lean_object* v___y_622_ = _args[10];
lean_object* v___y_623_ = _args[11];
lean_object* v___y_624_ = _args[12];
lean_object* v___y_625_ = _args[13];
lean_object* v___y_626_ = _args[14];
lean_object* v___y_627_ = _args[15];
lean_object* v___y_628_ = _args[16];
lean_object* v___y_629_ = _args[17];
lean_object* v___y_630_ = _args[18];
_start:
{
size_t v_sz_boxed_631_; size_t v_i_boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_613_);
lean_dec(v_sz_613_);
v_i_boxed_632_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_612_, v_sz_boxed_631_, v_i_boxed_632_, v_b_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_as_612_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(lean_object* v_as_634_, size_t v_i_635_, size_t v_stop_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_usize_dec_eq(v_i_635_, v_stop_636_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_array_uget_borrowed(v_as_634_, v_i_635_);
lean_inc(v___x_646_);
v___x_647_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_637_, v___x_646_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; size_t v___x_649_; size_t v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_635_, v___x_649_);
v_i_635_ = v___x_650_;
v_b_637_ = v_a_648_;
goto _start;
}
else
{
return v___x_647_;
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_b_637_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg___boxed(lean_object* v_as_653_, lean_object* v_i_654_, lean_object* v_stop_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
size_t v_i_boxed_664_; size_t v_stop_boxed_665_; lean_object* v_res_666_; 
v_i_boxed_664_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_stop_boxed_665_ = lean_unbox_usize(v_stop_655_);
lean_dec(v_stop_655_);
v_res_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_653_, v_i_boxed_664_, v_stop_boxed_665_, v_b_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v_as_653_);
return v_res_666_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1(void){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2);
v___x_674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
lean_ctor_set(v___x_674_, 2, v___x_673_);
lean_ctor_set(v___x_674_, 3, v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_box(0);
v___x_676_ = lean_unsigned_to_nat(16u);
v___x_677_ = lean_mk_array(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
v___x_682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_ctor_set(v___x_682_, 2, v___x_681_);
lean_ctor_set(v___x_682_, 3, v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_700_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16));
v___x_701_ = l_Lean_Name_append(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18(void){
_start:
{
lean_object* v___x_702_; double v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(1000000000u);
v___x_703_ = lean_float_of_nat(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___y_720_; lean_object* v_a_721_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v_hypQueue_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v_toCold_931_; lean_object* v_options_932_; uint8_t v_hasTrace_933_; 
v_toCold_931_ = lean_ctor_get(v_a_716_, 0);
v_options_932_ = lean_ctor_get(v_toCold_931_, 2);
v_hasTrace_933_ = lean_ctor_get_uint8(v_options_932_, sizeof(void*)*1);
if (v_hasTrace_933_ == 0)
{
lean_object* v___x_934_; lean_object* v_satExpr_935_; lean_object* v_hypQueue_936_; lean_object* v_usedHyps_937_; uint8_t v_didChange_938_; lean_object* v_theoryState_939_; lean_object* v_solverTimeBudgetMs_940_; lean_object* v_roundBudget_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v___x_934_ = lean_st_ref_take(v_a_705_);
v_satExpr_935_ = lean_ctor_get(v___x_934_, 0);
v_hypQueue_936_ = lean_ctor_get(v___x_934_, 1);
v_usedHyps_937_ = lean_ctor_get(v___x_934_, 2);
v_didChange_938_ = lean_ctor_get_uint8(v___x_934_, sizeof(void*)*6);
v_theoryState_939_ = lean_ctor_get(v___x_934_, 3);
v_solverTimeBudgetMs_940_ = lean_ctor_get(v___x_934_, 4);
v_roundBudget_941_ = lean_ctor_get(v___x_934_, 5);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v___x_934_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_roundBudget_941_);
lean_inc(v_solverTimeBudgetMs_940_);
lean_inc(v_theoryState_939_);
lean_inc(v_usedHyps_937_);
lean_inc(v_hypQueue_936_);
lean_inc(v_satExpr_935_);
lean_dec(v___x_934_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_946_ = l_Array_append___redArg(v_usedHyps_937_, v_hypQueue_936_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 2, v___x_946_);
lean_ctor_set(v___x_943_, 1, v___x_945_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_satExpr_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_theoryState_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_solverTimeBudgetMs_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_roundBudget_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*6, v_didChange_938_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_st_ref_put(v_a_705_, v___x_948_);
v_hypQueue_754_ = v_hypQueue_936_;
v___y_755_ = v_a_704_;
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
goto v___jp_753_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_952_; lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v_a_976_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v_a_982_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v_a_1003_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v_a_1014_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v_a_1026_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v_a_1032_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v_a_1053_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; 
v_inheritedTraceOptions_952_ = lean_ctor_get(v_toCold_931_, 11);
v___f_953_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_954_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_955_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_956_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_952_, v_options_932_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = l_Lean_trace_profiler;
v___x_1373_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_932_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v_satExpr_1375_; lean_object* v_hypQueue_1376_; lean_object* v_usedHyps_1377_; uint8_t v_didChange_1378_; lean_object* v_theoryState_1379_; lean_object* v_solverTimeBudgetMs_1380_; lean_object* v_roundBudget_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v___x_1374_ = lean_st_ref_take(v_a_705_);
v_satExpr_1375_ = lean_ctor_get(v___x_1374_, 0);
v_hypQueue_1376_ = lean_ctor_get(v___x_1374_, 1);
v_usedHyps_1377_ = lean_ctor_get(v___x_1374_, 2);
v_didChange_1378_ = lean_ctor_get_uint8(v___x_1374_, sizeof(void*)*6);
v_theoryState_1379_ = lean_ctor_get(v___x_1374_, 3);
v_solverTimeBudgetMs_1380_ = lean_ctor_get(v___x_1374_, 4);
v_roundBudget_1381_ = lean_ctor_get(v___x_1374_, 5);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1383_ = v___x_1374_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_roundBudget_1381_);
lean_inc(v_solverTimeBudgetMs_1380_);
lean_inc(v_theoryState_1379_);
lean_inc(v_usedHyps_1377_);
lean_inc(v_hypQueue_1376_);
lean_inc(v_satExpr_1375_);
lean_dec(v___x_1374_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1386_ = l_Array_append___redArg(v_usedHyps_1377_, v_hypQueue_1376_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 2, v___x_1386_);
lean_ctor_set(v___x_1383_, 1, v___x_1385_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_satExpr_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_theoryState_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_solverTimeBudgetMs_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_roundBudget_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*6, v_didChange_1378_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_st_ref_put(v_a_705_, v___x_1388_);
v_hypQueue_754_ = v_hypQueue_1376_;
v___y_755_ = v_a_704_;
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
goto v___jp_753_;
}
}
}
else
{
goto v___jp_1061_;
}
}
else
{
goto v___jp_1061_;
}
v___jp_958_:
{
lean_object* v___x_962_; double v___x_963_; double v___x_964_; double v___x_965_; double v___x_966_; double v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_962_ = lean_io_mono_nanos_now();
v___x_963_ = lean_float_of_nat(v___y_960_);
v___x_964_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
v___x_965_ = lean_float_div(v___x_963_, v___x_964_);
v___x_966_ = lean_float_of_nat(v___x_962_);
v___x_967_ = lean_float_div(v___x_966_, v___x_964_);
v___x_968_ = lean_box_float(v___x_965_);
v___x_969_ = lean_box_float(v___x_967_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_a_961_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_954_, v_hasTrace_933_, v___x_955_, v_options_932_, v___x_957_, v___y_959_, v___f_953_, v___x_971_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_972_;
}
v___jp_973_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_box(v_a_976_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___y_959_ = v___y_974_;
v___y_960_ = v___y_975_;
v_a_961_ = v___x_978_;
goto v___jp_958_;
}
v___jp_979_:
{
lean_object* v___x_983_; lean_object* v_hypQueue_984_; lean_object* v_usedHyps_985_; uint8_t v_didChange_986_; lean_object* v_theoryState_987_; lean_object* v_solverTimeBudgetMs_988_; lean_object* v_roundBudget_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v___x_983_ = lean_st_ref_take(v_a_705_);
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
v___x_995_ = lean_st_ref_put(v_a_705_, v___x_994_);
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
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_a_1003_);
v___y_959_ = v___y_1001_;
v___y_960_ = v___y_1002_;
v_a_961_ = v___x_1004_;
goto v___jp_958_;
}
v___jp_1005_:
{
if (lean_obj_tag(v___y_1008_) == 0)
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v___y_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___y_1008_, 1);
v___y_980_ = v___y_1006_;
v___y_981_ = v___y_1007_;
v_a_982_ = v_a_1009_;
goto v___jp_979_;
}
else
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___y_1008_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___y_1008_, 1);
v___y_1001_ = v___y_1006_;
v___y_1002_ = v___y_1007_;
v_a_1003_ = v_a_1010_;
goto v___jp_1000_;
}
}
v___jp_1011_:
{
lean_object* v___x_1015_; double v___x_1016_; double v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1015_ = lean_io_get_num_heartbeats();
v___x_1016_ = lean_float_of_nat(v___y_1012_);
v___x_1017_ = lean_float_of_nat(v___x_1015_);
v___x_1018_ = lean_box_float(v___x_1016_);
v___x_1019_ = lean_box_float(v___x_1017_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_a_1014_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_954_, v_hasTrace_933_, v___x_955_, v_options_932_, v___x_957_, v___y_1013_, v___f_953_, v___x_1021_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_1022_;
}
v___jp_1023_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(v_a_1026_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___y_1012_ = v___y_1024_;
v___y_1013_ = v___y_1025_;
v_a_1014_ = v___x_1028_;
goto v___jp_1011_;
}
v___jp_1029_:
{
lean_object* v___x_1033_; lean_object* v_hypQueue_1034_; lean_object* v_usedHyps_1035_; uint8_t v_didChange_1036_; lean_object* v_theoryState_1037_; lean_object* v_solverTimeBudgetMs_1038_; lean_object* v_roundBudget_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1048_; 
v___x_1033_ = lean_st_ref_take(v_a_705_);
v_hypQueue_1034_ = lean_ctor_get(v___x_1033_, 1);
v_usedHyps_1035_ = lean_ctor_get(v___x_1033_, 2);
v_didChange_1036_ = lean_ctor_get_uint8(v___x_1033_, sizeof(void*)*6);
v_theoryState_1037_ = lean_ctor_get(v___x_1033_, 3);
v_solverTimeBudgetMs_1038_ = lean_ctor_get(v___x_1033_, 4);
v_roundBudget_1039_ = lean_ctor_get(v___x_1033_, 5);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1049_);
v___x_1041_ = v___x_1033_;
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_roundBudget_1039_);
lean_inc(v_solverTimeBudgetMs_1038_);
lean_inc(v_theoryState_1037_);
lean_inc(v_usedHyps_1035_);
lean_inc(v_hypQueue_1034_);
lean_dec(v___x_1033_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_a_1032_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1032_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_hypQueue_1034_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_usedHyps_1035_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_theoryState_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_solverTimeBudgetMs_1038_);
lean_ctor_set(v_reuseFailAlloc_1047_, 5, v_roundBudget_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*6, v_didChange_1036_);
v___x_1044_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_st_ref_put(v_a_705_, v___x_1044_);
v___x_1046_ = 1;
v___y_1024_ = v___y_1030_;
v___y_1025_ = v___y_1031_;
v_a_1026_ = v___x_1046_;
goto v___jp_1023_;
}
}
}
v___jp_1050_:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_a_1053_);
v___y_1012_ = v___y_1051_;
v___y_1013_ = v___y_1052_;
v_a_1014_ = v___x_1054_;
goto v___jp_1011_;
}
v___jp_1055_:
{
if (lean_obj_tag(v___y_1058_) == 0)
{
lean_object* v_a_1059_; 
v_a_1059_ = lean_ctor_get(v___y_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___y_1058_, 1);
v___y_1030_ = v___y_1056_;
v___y_1031_ = v___y_1057_;
v_a_1032_ = v_a_1059_;
goto v___jp_1029_;
}
else
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___y_1058_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___y_1058_, 1);
v___y_1051_ = v___y_1056_;
v___y_1052_ = v___y_1057_;
v_a_1053_ = v_a_1060_;
goto v___jp_1050_;
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1371_; 
v___x_1062_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v_a_717_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1371_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1371_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1068_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_932_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v_satExpr_1071_; lean_object* v_hypQueue_1072_; lean_object* v_usedHyps_1073_; uint8_t v_didChange_1074_; lean_object* v_theoryState_1075_; lean_object* v_solverTimeBudgetMs_1076_; lean_object* v_roundBudget_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1219_; 
v___x_1069_ = lean_io_mono_nanos_now();
v___x_1070_ = lean_st_ref_take(v_a_705_);
v_satExpr_1071_ = lean_ctor_get(v___x_1070_, 0);
v_hypQueue_1072_ = lean_ctor_get(v___x_1070_, 1);
v_usedHyps_1073_ = lean_ctor_get(v___x_1070_, 2);
v_didChange_1074_ = lean_ctor_get_uint8(v___x_1070_, sizeof(void*)*6);
v_theoryState_1075_ = lean_ctor_get(v___x_1070_, 3);
v_solverTimeBudgetMs_1076_ = lean_ctor_get(v___x_1070_, 4);
v_roundBudget_1077_ = lean_ctor_get(v___x_1070_, 5);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1079_ = v___x_1070_;
v_isShared_1080_ = v_isSharedCheck_1219_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_roundBudget_1077_);
lean_inc(v_solverTimeBudgetMs_1076_);
lean_inc(v_theoryState_1075_);
lean_inc(v_usedHyps_1073_);
lean_inc(v_hypQueue_1072_);
lean_inc(v_satExpr_1071_);
lean_dec(v___x_1070_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1219_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1083_ = l_Array_append___redArg(v_usedHyps_1073_, v_hypQueue_1072_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 2, v___x_1083_);
lean_ctor_set(v___x_1079_, 1, v___x_1082_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_satExpr_1071_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_theoryState_1075_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_solverTimeBudgetMs_1076_);
lean_ctor_set(v_reuseFailAlloc_1218_, 5, v_roundBudget_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*6, v_didChange_1074_);
v___x_1085_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_st_ref_put(v_a_705_, v___x_1085_);
v___x_1087_ = lean_array_get_size(v_hypQueue_1072_);
v___x_1088_ = lean_nat_dec_eq(v___x_1087_, v___x_1081_);
if (v___x_1088_ == 0)
{
lean_object* v_goal_1089_; lean_object* v_tacticContext_1090_; lean_object* v___x_1091_; lean_object* v_config_1092_; lean_object* v_mode_1093_; lean_object* v_timeout_1094_; uint8_t v_trimProofs_1095_; uint8_t v_binaryProofs_1096_; uint8_t v_acNf_1097_; uint8_t v_andFlattening_1098_; uint8_t v_embeddedConstraintSubst_1099_; uint8_t v_graphviz_1100_; lean_object* v_maxSteps_1101_; uint8_t v_solverMode_1102_; uint8_t v_uf_1103_; lean_object* v_cegarRounds_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1216_; 
v_goal_1089_ = lean_ctor_get(v_a_704_, 0);
v_tacticContext_1090_ = lean_ctor_get(v_a_704_, 2);
lean_inc_ref(v_tacticContext_1090_);
v___x_1091_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1090_);
v_config_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_config_1092_);
v_mode_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_mode_1093_);
lean_dec_ref(v___x_1091_);
v_timeout_1094_ = lean_ctor_get(v_config_1092_, 0);
v_trimProofs_1095_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3);
v_binaryProofs_1096_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 1);
v_acNf_1097_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 2);
v_andFlattening_1098_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1099_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 4);
v_graphviz_1100_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 8);
v_maxSteps_1101_ = lean_ctor_get(v_config_1092_, 1);
v_solverMode_1102_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 10);
v_uf_1103_ = lean_ctor_get_uint8(v_config_1092_, sizeof(void*)*3 + 11);
v_cegarRounds_1104_ = lean_ctor_get(v_config_1092_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_config_1092_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1106_ = v_config_1092_;
v_isShared_1107_ = v_isSharedCheck_1216_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_cegarRounds_1104_);
lean_inc(v_maxSteps_1101_);
lean_inc(v_timeout_1094_);
lean_dec(v_config_1092_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1216_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
lean_inc(v_goal_1089_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_goal_1089_);
v___x_1109_ = v___x_1065_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_goal_1089_);
v___x_1109_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1107_ == 0)
{
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_timeout_1094_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_maxSteps_1101_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_cegarRounds_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3, v_trimProofs_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 1, v_binaryProofs_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 2, v_acNf_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 3, v_andFlattening_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 8, v_graphviz_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 10, v_solverMode_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 11, v_uf_1103_);
v___x_1111_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_theoryState_1116_; lean_object* v_satExpr_1117_; lean_object* v_hypQueue_1118_; lean_object* v_usedHyps_1119_; uint8_t v_didChange_1120_; lean_object* v_solverTimeBudgetMs_1121_; lean_object* v_roundBudget_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1213_; 
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 5, v___x_1088_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 6, v___x_1088_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 7, v___x_1088_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 9, v___x_1088_);
v___x_1112_ = lean_box(v_hasTrace_933_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
v___x_1114_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1093_, v___x_1111_, v___x_1113_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = lean_st_ref_take(v_a_705_);
v_theoryState_1116_ = lean_ctor_get(v___x_1115_, 3);
v_satExpr_1117_ = lean_ctor_get(v___x_1115_, 0);
v_hypQueue_1118_ = lean_ctor_get(v___x_1115_, 1);
v_usedHyps_1119_ = lean_ctor_get(v___x_1115_, 2);
v_didChange_1120_ = lean_ctor_get_uint8(v___x_1115_, sizeof(void*)*6);
v_solverTimeBudgetMs_1121_ = lean_ctor_get(v___x_1115_, 4);
v_roundBudget_1122_ = lean_ctor_get(v___x_1115_, 5);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1124_ = v___x_1115_;
v_isShared_1125_ = v_isSharedCheck_1213_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_roundBudget_1122_);
lean_inc(v_solverTimeBudgetMs_1121_);
lean_inc(v_theoryState_1116_);
lean_inc(v_usedHyps_1119_);
lean_inc(v_hypQueue_1118_);
lean_inc(v_satExpr_1117_);
lean_dec(v___x_1115_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1213_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_funState_1126_; lean_object* v_bitvecState_1127_; lean_object* v_preprocessCaches_1128_; lean_object* v_satSolver_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1212_; 
v_funState_1126_ = lean_ctor_get(v_theoryState_1116_, 0);
v_bitvecState_1127_ = lean_ctor_get(v_theoryState_1116_, 1);
v_preprocessCaches_1128_ = lean_ctor_get(v_theoryState_1116_, 2);
v_satSolver_1129_ = lean_ctor_get(v_theoryState_1116_, 3);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_theoryState_1116_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1131_ = v_theoryState_1116_;
v_isShared_1132_ = v_isSharedCheck_1212_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_satSolver_1129_);
lean_inc(v_preprocessCaches_1128_);
lean_inc(v_bitvecState_1127_);
lean_inc(v_funState_1126_);
lean_dec(v_theoryState_1116_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1212_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 2, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_funState_1126_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_bitvecState_1127_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_satSolver_1129_);
v___x_1135_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 3, v___x_1135_);
v___x_1137_ = v___x_1124_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_satExpr_1117_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_hypQueue_1118_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_usedHyps_1119_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_solverTimeBudgetMs_1121_);
lean_ctor_set(v_reuseFailAlloc_1210_, 5, v_roundBudget_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*6, v_didChange_1120_);
v___x_1137_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_typeAnalysis_1143_; lean_object* v_target_1144_; lean_object* v_hypotheses_1145_; uint8_t v_didChange_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1208_; 
v___x_1138_ = lean_st_ref_put(v_a_705_, v___x_1137_);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1140_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1140_, 0, v___x_1133_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
lean_ctor_set(v___x_1140_, 2, v___x_1109_);
lean_ctor_set(v___x_1140_, 3, v___x_1082_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*4, v___x_1088_);
v___x_1141_ = lean_st_mk_ref(v___x_1140_);
v___x_1142_ = lean_st_ref_take(v___x_1141_);
v_typeAnalysis_1143_ = lean_ctor_get(v___x_1142_, 1);
v_target_1144_ = lean_ctor_get(v___x_1142_, 2);
v_hypotheses_1145_ = lean_ctor_get(v___x_1142_, 3);
v_didChange_1146_ = lean_ctor_get_uint8(v___x_1142_, sizeof(void*)*4);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1142_, 0);
lean_dec(v_unused_1209_);
v___x_1148_ = v___x_1142_;
v_isShared_1149_ = v_isSharedCheck_1208_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_hypotheses_1145_);
lean_inc(v_target_1144_);
lean_inc(v_typeAnalysis_1143_);
lean_dec(v___x_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1208_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_preprocessCaches_1128_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_preprocessCaches_1128_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_typeAnalysis_1143_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_target_1144_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_hypotheses_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*4, v_didChange_1146_);
v___x_1151_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = lean_st_ref_put(v___x_1141_, v___x_1151_);
v_sz_1153_ = lean_array_size(v_hypQueue_1072_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1153_, v___x_1154_, v_hypQueue_1072_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1156_, v___x_1114_, v___x_1141_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v___x_1114_);
lean_dec_ref_known(v___x_1156_, 1);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = lean_st_ref_get(v___x_1141_);
lean_dec(v___x_1141_);
v___x_1160_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1160_ == 0)
{
lean_object* v_caches_1161_; lean_object* v_hypotheses_1162_; lean_object* v___x_1163_; lean_object* v_theoryState_1164_; lean_object* v_satExpr_1165_; lean_object* v_hypQueue_1166_; lean_object* v_usedHyps_1167_; uint8_t v_didChange_1168_; lean_object* v_solverTimeBudgetMs_1169_; lean_object* v_roundBudget_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1204_; 
v_caches_1161_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_caches_1161_);
v_hypotheses_1162_ = lean_ctor_get(v___x_1159_, 3);
lean_inc_ref(v_hypotheses_1162_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_st_ref_take(v_a_705_);
v_theoryState_1164_ = lean_ctor_get(v___x_1163_, 3);
v_satExpr_1165_ = lean_ctor_get(v___x_1163_, 0);
v_hypQueue_1166_ = lean_ctor_get(v___x_1163_, 1);
v_usedHyps_1167_ = lean_ctor_get(v___x_1163_, 2);
v_didChange_1168_ = lean_ctor_get_uint8(v___x_1163_, sizeof(void*)*6);
v_solverTimeBudgetMs_1169_ = lean_ctor_get(v___x_1163_, 4);
v_roundBudget_1170_ = lean_ctor_get(v___x_1163_, 5);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1172_ = v___x_1163_;
v_isShared_1173_ = v_isSharedCheck_1204_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_roundBudget_1170_);
lean_inc(v_solverTimeBudgetMs_1169_);
lean_inc(v_theoryState_1164_);
lean_inc(v_usedHyps_1167_);
lean_inc(v_hypQueue_1166_);
lean_inc(v_satExpr_1165_);
lean_dec(v___x_1163_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1204_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_funState_1174_; lean_object* v_bitvecState_1175_; lean_object* v_satSolver_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1202_; 
v_funState_1174_ = lean_ctor_get(v_theoryState_1164_, 0);
v_bitvecState_1175_ = lean_ctor_get(v_theoryState_1164_, 1);
v_satSolver_1176_ = lean_ctor_get(v_theoryState_1164_, 3);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_theoryState_1164_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_theoryState_1164_, 2);
lean_dec(v_unused_1203_);
v___x_1178_ = v_theoryState_1164_;
v_isShared_1179_ = v_isSharedCheck_1202_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_satSolver_1176_);
lean_inc(v_bitvecState_1175_);
lean_inc(v_funState_1174_);
lean_dec(v_theoryState_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1202_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 2, v_caches_1161_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_funState_1174_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_bitvecState_1175_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_caches_1161_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_satSolver_1176_);
v___x_1181_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 3, v___x_1181_);
v___x_1183_ = v___x_1172_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_satExpr_1165_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_hypQueue_1166_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_usedHyps_1167_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_solverTimeBudgetMs_1169_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_roundBudget_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*6, v_didChange_1168_);
v___x_1183_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; size_t v_sz_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_st_ref_put(v_a_705_, v___x_1183_);
v_sz_1185_ = lean_array_size(v_hypotheses_1162_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1162_, v_sz_1185_, v___x_1154_, v___x_1082_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v_hypotheses_1162_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = lean_array_get_size(v_a_1187_);
v___x_1189_ = lean_nat_dec_eq(v___x_1188_, v___x_1081_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_satExpr_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_st_ref_get(v_a_705_);
v_satExpr_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_satExpr_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_nat_dec_lt(v___x_1081_, v___x_1188_);
if (v___x_1192_ == 0)
{
lean_dec(v_a_1187_);
v___y_980_ = v_a_1063_;
v___y_981_ = v___x_1069_;
v_a_982_ = v_satExpr_1191_;
goto v___jp_979_;
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_le(v___x_1188_, v___x_1188_);
if (v___x_1193_ == 0)
{
if (v___x_1192_ == 0)
{
lean_dec(v_a_1187_);
v___y_980_ = v_a_1063_;
v___y_981_ = v___x_1069_;
v_a_982_ = v_satExpr_1191_;
goto v___jp_979_;
}
else
{
size_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_usize_of_nat(v___x_1188_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1187_, v___x_1154_, v___x_1194_, v_satExpr_1191_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_1187_);
v___y_1006_ = v_a_1063_;
v___y_1007_ = v___x_1069_;
v___y_1008_ = v___x_1195_;
goto v___jp_1005_;
}
}
else
{
size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_usize_of_nat(v___x_1188_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1187_, v___x_1154_, v___x_1196_, v_satExpr_1191_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_1187_);
v___y_1006_ = v_a_1063_;
v___y_1007_ = v___x_1069_;
v___y_1008_ = v___x_1197_;
goto v___jp_1005_;
}
}
}
else
{
uint8_t v___x_1198_; 
lean_dec(v_a_1187_);
v___x_1198_ = 2;
v___y_974_ = v_a_1063_;
v___y_975_ = v___x_1069_;
v_a_976_ = v___x_1198_;
goto v___jp_973_;
}
}
else
{
lean_object* v_a_1199_; 
v_a_1199_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1186_, 1);
v___y_1001_ = v_a_1063_;
v___y_1002_ = v___x_1069_;
v_a_1003_ = v_a_1199_;
goto v___jp_1000_;
}
}
}
}
}
}
else
{
uint8_t v___x_1205_; 
lean_dec(v___x_1159_);
v___x_1205_ = 0;
v___y_974_ = v_a_1063_;
v___y_975_ = v___x_1069_;
v_a_976_ = v___x_1205_;
goto v___jp_973_;
}
}
else
{
lean_object* v_a_1206_; 
lean_dec(v___x_1141_);
v_a_1206_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1157_, 1);
v___y_1001_ = v_a_1063_;
v___y_1002_ = v___x_1069_;
v_a_1003_ = v_a_1206_;
goto v___jp_1000_;
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
uint8_t v___x_1217_; 
lean_dec_ref(v_hypQueue_1072_);
lean_del_object(v___x_1065_);
v___x_1217_ = 2;
v___y_974_ = v_a_1063_;
v___y_975_ = v___x_1069_;
v_a_976_ = v___x_1217_;
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_satExpr_1222_; lean_object* v_hypQueue_1223_; lean_object* v_usedHyps_1224_; uint8_t v_didChange_1225_; lean_object* v_theoryState_1226_; lean_object* v_solverTimeBudgetMs_1227_; lean_object* v_roundBudget_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1370_; 
v___x_1220_ = lean_io_get_num_heartbeats();
v___x_1221_ = lean_st_ref_take(v_a_705_);
v_satExpr_1222_ = lean_ctor_get(v___x_1221_, 0);
v_hypQueue_1223_ = lean_ctor_get(v___x_1221_, 1);
v_usedHyps_1224_ = lean_ctor_get(v___x_1221_, 2);
v_didChange_1225_ = lean_ctor_get_uint8(v___x_1221_, sizeof(void*)*6);
v_theoryState_1226_ = lean_ctor_get(v___x_1221_, 3);
v_solverTimeBudgetMs_1227_ = lean_ctor_get(v___x_1221_, 4);
v_roundBudget_1228_ = lean_ctor_get(v___x_1221_, 5);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1230_ = v___x_1221_;
v_isShared_1231_ = v_isSharedCheck_1370_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_roundBudget_1228_);
lean_inc(v_solverTimeBudgetMs_1227_);
lean_inc(v_theoryState_1226_);
lean_inc(v_usedHyps_1224_);
lean_inc(v_hypQueue_1223_);
lean_inc(v_satExpr_1222_);
lean_dec(v___x_1221_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1370_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1234_ = l_Array_append___redArg(v_usedHyps_1224_, v_hypQueue_1223_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 2, v___x_1234_);
lean_ctor_set(v___x_1230_, 1, v___x_1233_);
v___x_1236_ = v___x_1230_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_satExpr_1222_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_theoryState_1226_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_solverTimeBudgetMs_1227_);
lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_roundBudget_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*6, v_didChange_1225_);
v___x_1236_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = lean_st_ref_put(v_a_705_, v___x_1236_);
v___x_1238_ = lean_array_get_size(v_hypQueue_1223_);
v___x_1239_ = lean_nat_dec_eq(v___x_1238_, v___x_1232_);
if (v___x_1239_ == 0)
{
lean_object* v_goal_1240_; lean_object* v_tacticContext_1241_; lean_object* v___x_1242_; lean_object* v_config_1243_; lean_object* v_mode_1244_; lean_object* v_timeout_1245_; uint8_t v_trimProofs_1246_; uint8_t v_binaryProofs_1247_; uint8_t v_acNf_1248_; uint8_t v_andFlattening_1249_; uint8_t v_embeddedConstraintSubst_1250_; uint8_t v_graphviz_1251_; lean_object* v_maxSteps_1252_; uint8_t v_solverMode_1253_; uint8_t v_uf_1254_; lean_object* v_cegarRounds_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1367_; 
v_goal_1240_ = lean_ctor_get(v_a_704_, 0);
v_tacticContext_1241_ = lean_ctor_get(v_a_704_, 2);
lean_inc_ref(v_tacticContext_1241_);
v___x_1242_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1241_);
v_config_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_config_1243_);
v_mode_1244_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_mode_1244_);
lean_dec_ref(v___x_1242_);
v_timeout_1245_ = lean_ctor_get(v_config_1243_, 0);
v_trimProofs_1246_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3);
v_binaryProofs_1247_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 1);
v_acNf_1248_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 2);
v_andFlattening_1249_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1250_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 4);
v_graphviz_1251_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 8);
v_maxSteps_1252_ = lean_ctor_get(v_config_1243_, 1);
v_solverMode_1253_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 10);
v_uf_1254_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*3 + 11);
v_cegarRounds_1255_ = lean_ctor_get(v_config_1243_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_config_1243_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1257_ = v_config_1243_;
v_isShared_1258_ = v_isSharedCheck_1367_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_cegarRounds_1255_);
lean_inc(v_maxSteps_1252_);
lean_inc(v_timeout_1245_);
lean_dec(v_config_1243_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1367_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
lean_inc(v_goal_1240_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_goal_1240_);
v___x_1260_ = v___x_1065_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_goal_1240_);
v___x_1260_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1258_ == 0)
{
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_timeout_1245_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_maxSteps_1252_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_cegarRounds_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3, v_trimProofs_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 1, v_binaryProofs_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 2, v_acNf_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 3, v_andFlattening_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 8, v_graphviz_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 10, v_solverMode_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*3 + 11, v_uf_1254_);
v___x_1262_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_theoryState_1267_; lean_object* v_satExpr_1268_; lean_object* v_hypQueue_1269_; lean_object* v_usedHyps_1270_; uint8_t v_didChange_1271_; lean_object* v_solverTimeBudgetMs_1272_; lean_object* v_roundBudget_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1364_; 
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 5, v___x_1239_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 6, v___x_1239_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 7, v___x_1239_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 9, v___x_1239_);
v___x_1263_ = lean_box(v___x_1068_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
v___x_1265_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1244_, v___x_1262_, v___x_1264_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = lean_st_ref_take(v_a_705_);
v_theoryState_1267_ = lean_ctor_get(v___x_1266_, 3);
v_satExpr_1268_ = lean_ctor_get(v___x_1266_, 0);
v_hypQueue_1269_ = lean_ctor_get(v___x_1266_, 1);
v_usedHyps_1270_ = lean_ctor_get(v___x_1266_, 2);
v_didChange_1271_ = lean_ctor_get_uint8(v___x_1266_, sizeof(void*)*6);
v_solverTimeBudgetMs_1272_ = lean_ctor_get(v___x_1266_, 4);
v_roundBudget_1273_ = lean_ctor_get(v___x_1266_, 5);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1275_ = v___x_1266_;
v_isShared_1276_ = v_isSharedCheck_1364_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_roundBudget_1273_);
lean_inc(v_solverTimeBudgetMs_1272_);
lean_inc(v_theoryState_1267_);
lean_inc(v_usedHyps_1270_);
lean_inc(v_hypQueue_1269_);
lean_inc(v_satExpr_1268_);
lean_dec(v___x_1266_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1364_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_funState_1277_; lean_object* v_bitvecState_1278_; lean_object* v_preprocessCaches_1279_; lean_object* v_satSolver_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1363_; 
v_funState_1277_ = lean_ctor_get(v_theoryState_1267_, 0);
v_bitvecState_1278_ = lean_ctor_get(v_theoryState_1267_, 1);
v_preprocessCaches_1279_ = lean_ctor_get(v_theoryState_1267_, 2);
v_satSolver_1280_ = lean_ctor_get(v_theoryState_1267_, 3);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_theoryState_1267_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1282_ = v_theoryState_1267_;
v_isShared_1283_ = v_isSharedCheck_1363_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_satSolver_1280_);
lean_inc(v_preprocessCaches_1279_);
lean_inc(v_bitvecState_1278_);
lean_inc(v_funState_1277_);
lean_dec(v_theoryState_1267_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1363_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 2, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_funState_1277_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_bitvecState_1278_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_satSolver_1280_);
v___x_1286_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 3, v___x_1286_);
v___x_1288_ = v___x_1275_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_satExpr_1268_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_hypQueue_1269_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_usedHyps_1270_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_solverTimeBudgetMs_1272_);
lean_ctor_set(v_reuseFailAlloc_1361_, 5, v_roundBudget_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, sizeof(void*)*6, v_didChange_1271_);
v___x_1288_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_typeAnalysis_1294_; lean_object* v_target_1295_; lean_object* v_hypotheses_1296_; uint8_t v_didChange_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1359_; 
v___x_1289_ = lean_st_ref_put(v_a_705_, v___x_1288_);
v___x_1290_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1291_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1291_, 0, v___x_1284_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1260_);
lean_ctor_set(v___x_1291_, 3, v___x_1233_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*4, v___x_1239_);
v___x_1292_ = lean_st_mk_ref(v___x_1291_);
v___x_1293_ = lean_st_ref_take(v___x_1292_);
v_typeAnalysis_1294_ = lean_ctor_get(v___x_1293_, 1);
v_target_1295_ = lean_ctor_get(v___x_1293_, 2);
v_hypotheses_1296_ = lean_ctor_get(v___x_1293_, 3);
v_didChange_1297_ = lean_ctor_get_uint8(v___x_1293_, sizeof(void*)*4);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1360_);
v___x_1299_ = v___x_1293_;
v_isShared_1300_ = v_isSharedCheck_1359_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_hypotheses_1296_);
lean_inc(v_target_1295_);
lean_inc(v_typeAnalysis_1294_);
lean_dec(v___x_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1359_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_preprocessCaches_1279_);
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_preprocessCaches_1279_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_typeAnalysis_1294_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_target_1295_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_hypotheses_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*4, v_didChange_1297_);
v___x_1302_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; size_t v_sz_1304_; size_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1303_ = lean_st_ref_put(v___x_1292_, v___x_1302_);
v_sz_1304_ = lean_array_size(v_hypQueue_1223_);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1304_, v___x_1305_, v_hypQueue_1223_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1307_, v___x_1265_, v___x_1292_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v___x_1265_);
lean_dec_ref_known(v___x_1307_, 1);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = lean_st_ref_get(v___x_1292_);
lean_dec(v___x_1292_);
v___x_1311_ = lean_unbox(v_a_1309_);
lean_dec(v_a_1309_);
if (v___x_1311_ == 0)
{
lean_object* v_caches_1312_; lean_object* v_hypotheses_1313_; lean_object* v___x_1314_; lean_object* v_theoryState_1315_; lean_object* v_satExpr_1316_; lean_object* v_hypQueue_1317_; lean_object* v_usedHyps_1318_; uint8_t v_didChange_1319_; lean_object* v_solverTimeBudgetMs_1320_; lean_object* v_roundBudget_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1355_; 
v_caches_1312_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_caches_1312_);
v_hypotheses_1313_ = lean_ctor_get(v___x_1310_, 3);
lean_inc_ref(v_hypotheses_1313_);
lean_dec(v___x_1310_);
v___x_1314_ = lean_st_ref_take(v_a_705_);
v_theoryState_1315_ = lean_ctor_get(v___x_1314_, 3);
v_satExpr_1316_ = lean_ctor_get(v___x_1314_, 0);
v_hypQueue_1317_ = lean_ctor_get(v___x_1314_, 1);
v_usedHyps_1318_ = lean_ctor_get(v___x_1314_, 2);
v_didChange_1319_ = lean_ctor_get_uint8(v___x_1314_, sizeof(void*)*6);
v_solverTimeBudgetMs_1320_ = lean_ctor_get(v___x_1314_, 4);
v_roundBudget_1321_ = lean_ctor_get(v___x_1314_, 5);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1323_ = v___x_1314_;
v_isShared_1324_ = v_isSharedCheck_1355_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_roundBudget_1321_);
lean_inc(v_solverTimeBudgetMs_1320_);
lean_inc(v_theoryState_1315_);
lean_inc(v_usedHyps_1318_);
lean_inc(v_hypQueue_1317_);
lean_inc(v_satExpr_1316_);
lean_dec(v___x_1314_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1355_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_funState_1325_; lean_object* v_bitvecState_1326_; lean_object* v_satSolver_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1353_; 
v_funState_1325_ = lean_ctor_get(v_theoryState_1315_, 0);
v_bitvecState_1326_ = lean_ctor_get(v_theoryState_1315_, 1);
v_satSolver_1327_ = lean_ctor_get(v_theoryState_1315_, 3);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_theoryState_1315_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v_theoryState_1315_, 2);
lean_dec(v_unused_1354_);
v___x_1329_ = v_theoryState_1315_;
v_isShared_1330_ = v_isSharedCheck_1353_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_satSolver_1327_);
lean_inc(v_bitvecState_1326_);
lean_inc(v_funState_1325_);
lean_dec(v_theoryState_1315_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1353_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 2, v_caches_1312_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_funState_1325_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_bitvecState_1326_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_caches_1312_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_satSolver_1327_);
v___x_1332_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 3, v___x_1332_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_satExpr_1316_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_hypQueue_1317_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_usedHyps_1318_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_solverTimeBudgetMs_1320_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_roundBudget_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6, v_didChange_1319_);
v___x_1334_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; size_t v_sz_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_st_ref_put(v_a_705_, v___x_1334_);
v_sz_1336_ = lean_array_size(v_hypotheses_1313_);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1313_, v_sz_1336_, v___x_1305_, v___x_1233_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v_hypotheses_1313_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1339_ = lean_array_get_size(v_a_1338_);
v___x_1340_ = lean_nat_dec_eq(v___x_1339_, v___x_1232_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v_satExpr_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_st_ref_get(v_a_705_);
v_satExpr_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref(v_satExpr_1342_);
lean_dec(v___x_1341_);
v___x_1343_ = lean_nat_dec_lt(v___x_1232_, v___x_1339_);
if (v___x_1343_ == 0)
{
lean_dec(v_a_1338_);
v___y_1030_ = v___x_1220_;
v___y_1031_ = v_a_1063_;
v_a_1032_ = v_satExpr_1342_;
goto v___jp_1029_;
}
else
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_nat_dec_le(v___x_1339_, v___x_1339_);
if (v___x_1344_ == 0)
{
if (v___x_1343_ == 0)
{
lean_dec(v_a_1338_);
v___y_1030_ = v___x_1220_;
v___y_1031_ = v_a_1063_;
v_a_1032_ = v_satExpr_1342_;
goto v___jp_1029_;
}
else
{
size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_usize_of_nat(v___x_1339_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1338_, v___x_1305_, v___x_1345_, v_satExpr_1342_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_1338_);
v___y_1056_ = v___x_1220_;
v___y_1057_ = v_a_1063_;
v___y_1058_ = v___x_1346_;
goto v___jp_1055_;
}
}
else
{
size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_usize_of_nat(v___x_1339_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1338_, v___x_1305_, v___x_1347_, v_satExpr_1342_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_1338_);
v___y_1056_ = v___x_1220_;
v___y_1057_ = v_a_1063_;
v___y_1058_ = v___x_1348_;
goto v___jp_1055_;
}
}
}
else
{
uint8_t v___x_1349_; 
lean_dec(v_a_1338_);
v___x_1349_ = 2;
v___y_1024_ = v___x_1220_;
v___y_1025_ = v_a_1063_;
v_a_1026_ = v___x_1349_;
goto v___jp_1023_;
}
}
else
{
lean_object* v_a_1350_; 
v_a_1350_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1337_, 1);
v___y_1051_ = v___x_1220_;
v___y_1052_ = v_a_1063_;
v_a_1053_ = v_a_1350_;
goto v___jp_1050_;
}
}
}
}
}
}
else
{
uint8_t v___x_1356_; 
lean_dec(v___x_1310_);
v___x_1356_ = 0;
v___y_1024_ = v___x_1220_;
v___y_1025_ = v_a_1063_;
v_a_1026_ = v___x_1356_;
goto v___jp_1023_;
}
}
else
{
lean_object* v_a_1357_; 
lean_dec(v___x_1292_);
v_a_1357_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1308_, 1);
v___y_1051_ = v___x_1220_;
v___y_1052_ = v_a_1063_;
v_a_1053_ = v_a_1357_;
goto v___jp_1050_;
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
uint8_t v___x_1368_; 
lean_dec_ref(v_hypQueue_1223_);
lean_del_object(v___x_1065_);
v___x_1368_ = 2;
v___y_1024_ = v___x_1220_;
v___y_1025_ = v_a_1063_;
v_a_1026_ = v___x_1368_;
goto v___jp_1023_;
}
}
}
}
}
}
}
v___jp_719_:
{
lean_object* v___x_722_; lean_object* v_hypQueue_723_; lean_object* v_usedHyps_724_; uint8_t v_didChange_725_; lean_object* v_theoryState_726_; lean_object* v_solverTimeBudgetMs_727_; lean_object* v_roundBudget_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v___x_722_ = lean_st_ref_take(v___y_720_);
v_hypQueue_723_ = lean_ctor_get(v___x_722_, 1);
v_usedHyps_724_ = lean_ctor_get(v___x_722_, 2);
v_didChange_725_ = lean_ctor_get_uint8(v___x_722_, sizeof(void*)*6);
v_theoryState_726_ = lean_ctor_get(v___x_722_, 3);
v_solverTimeBudgetMs_727_ = lean_ctor_get(v___x_722_, 4);
v_roundBudget_728_ = lean_ctor_get(v___x_722_, 5);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_740_);
v___x_730_ = v___x_722_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_roundBudget_728_);
lean_inc(v_solverTimeBudgetMs_727_);
lean_inc(v_theoryState_726_);
lean_inc(v_usedHyps_724_);
lean_inc(v_hypQueue_723_);
lean_dec(v___x_722_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_a_721_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_721_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_hypQueue_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_usedHyps_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_theoryState_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_solverTimeBudgetMs_727_);
lean_ctor_set(v_reuseFailAlloc_738_, 5, v_roundBudget_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*6, v_didChange_725_);
v___x_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_st_ref_put(v___y_720_, v___x_733_);
v___x_735_ = 1;
v___x_736_ = lean_box(v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
v___jp_741_:
{
if (lean_obj_tag(v___y_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___y_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___y_743_, 1);
v___y_720_ = v___y_742_;
v_a_721_ = v_a_744_;
goto v___jp_719_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___y_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___y_743_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___y_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
v___jp_753_:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_get_size(v_hypQueue_754_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v_goal_772_; lean_object* v_tacticContext_773_; lean_object* v___x_774_; lean_object* v_config_775_; lean_object* v_mode_776_; lean_object* v_timeout_777_; uint8_t v_trimProofs_778_; uint8_t v_binaryProofs_779_; uint8_t v_acNf_780_; uint8_t v_andFlattening_781_; uint8_t v_embeddedConstraintSubst_782_; uint8_t v_graphviz_783_; lean_object* v_maxSteps_784_; uint8_t v_solverMode_785_; uint8_t v_uf_786_; lean_object* v_cegarRounds_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_927_; 
v_goal_772_ = lean_ctor_get(v___y_755_, 0);
v_tacticContext_773_ = lean_ctor_get(v___y_755_, 2);
lean_inc_ref(v_tacticContext_773_);
v___x_774_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_773_);
v_config_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_config_775_);
v_mode_776_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_mode_776_);
lean_dec_ref(v___x_774_);
v_timeout_777_ = lean_ctor_get(v_config_775_, 0);
v_trimProofs_778_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3);
v_binaryProofs_779_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 1);
v_acNf_780_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 2);
v_andFlattening_781_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_782_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 4);
v_graphviz_783_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 8);
v_maxSteps_784_ = lean_ctor_get(v_config_775_, 1);
v_solverMode_785_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 10);
v_uf_786_ = lean_ctor_get_uint8(v_config_775_, sizeof(void*)*3 + 11);
v_cegarRounds_787_ = lean_ctor_get(v_config_775_, 2);
v_isSharedCheck_927_ = !lean_is_exclusive(v_config_775_);
if (v_isSharedCheck_927_ == 0)
{
v___x_789_ = v_config_775_;
v_isShared_790_ = v_isSharedCheck_927_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_cegarRounds_787_);
lean_inc(v_maxSteps_784_);
lean_inc(v_timeout_777_);
lean_dec(v_config_775_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_927_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc(v_goal_772_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_goal_772_);
if (v_isShared_790_ == 0)
{
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_timeout_777_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_maxSteps_784_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_cegarRounds_787_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3, v_trimProofs_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 1, v_binaryProofs_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 2, v_acNf_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 3, v_andFlattening_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 8, v_graphviz_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 10, v_solverMode_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 11, v_uf_786_);
v___x_793_ = v_reuseFailAlloc_926_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_theoryState_797_; lean_object* v_satExpr_798_; lean_object* v_hypQueue_799_; lean_object* v_usedHyps_800_; uint8_t v_didChange_801_; lean_object* v_solverTimeBudgetMs_802_; lean_object* v_roundBudget_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_925_; 
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*3 + 5, v___x_771_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*3 + 6, v___x_771_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*3 + 7, v___x_771_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*3 + 9, v___x_771_);
v___x_794_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_795_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_776_, v___x_793_, v___x_794_);
v___x_796_ = lean_st_ref_take(v___y_756_);
v_theoryState_797_ = lean_ctor_get(v___x_796_, 3);
v_satExpr_798_ = lean_ctor_get(v___x_796_, 0);
v_hypQueue_799_ = lean_ctor_get(v___x_796_, 1);
v_usedHyps_800_ = lean_ctor_get(v___x_796_, 2);
v_didChange_801_ = lean_ctor_get_uint8(v___x_796_, sizeof(void*)*6);
v_solverTimeBudgetMs_802_ = lean_ctor_get(v___x_796_, 4);
v_roundBudget_803_ = lean_ctor_get(v___x_796_, 5);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_925_ == 0)
{
v___x_805_ = v___x_796_;
v_isShared_806_ = v_isSharedCheck_925_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_roundBudget_803_);
lean_inc(v_solverTimeBudgetMs_802_);
lean_inc(v_theoryState_797_);
lean_inc(v_usedHyps_800_);
lean_inc(v_hypQueue_799_);
lean_inc(v_satExpr_798_);
lean_dec(v___x_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_925_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_funState_807_; lean_object* v_bitvecState_808_; lean_object* v_preprocessCaches_809_; lean_object* v_satSolver_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_924_; 
v_funState_807_ = lean_ctor_get(v_theoryState_797_, 0);
v_bitvecState_808_ = lean_ctor_get(v_theoryState_797_, 1);
v_preprocessCaches_809_ = lean_ctor_get(v_theoryState_797_, 2);
v_satSolver_810_ = lean_ctor_get(v_theoryState_797_, 3);
v_isSharedCheck_924_ = !lean_is_exclusive(v_theoryState_797_);
if (v_isSharedCheck_924_ == 0)
{
v___x_812_ = v_theoryState_797_;
v_isShared_813_ = v_isSharedCheck_924_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_satSolver_810_);
lean_inc(v_preprocessCaches_809_);
lean_inc(v_bitvecState_808_);
lean_inc(v_funState_807_);
lean_dec(v_theoryState_797_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_924_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 2, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_funState_807_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_bitvecState_808_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_satSolver_810_);
v___x_816_ = v_reuseFailAlloc_923_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 3, v___x_816_);
v___x_818_ = v___x_805_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_satExpr_798_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_hypQueue_799_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_usedHyps_800_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_solverTimeBudgetMs_802_);
lean_ctor_set(v_reuseFailAlloc_922_, 5, v_roundBudget_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*6, v_didChange_801_);
v___x_818_ = v_reuseFailAlloc_922_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_typeAnalysis_825_; lean_object* v_target_826_; lean_object* v_hypotheses_827_; uint8_t v_didChange_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_920_; 
v___x_819_ = lean_st_ref_put(v___y_756_, v___x_818_);
v___x_820_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_821_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7));
v___x_822_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_822_, 0, v___x_814_);
lean_ctor_set(v___x_822_, 1, v___x_820_);
lean_ctor_set(v___x_822_, 2, v___x_791_);
lean_ctor_set(v___x_822_, 3, v___x_821_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*4, v___x_771_);
v___x_823_ = lean_st_mk_ref(v___x_822_);
v___x_824_ = lean_st_ref_take(v___x_823_);
v_typeAnalysis_825_ = lean_ctor_get(v___x_824_, 1);
v_target_826_ = lean_ctor_get(v___x_824_, 2);
v_hypotheses_827_ = lean_ctor_get(v___x_824_, 3);
v_didChange_828_ = lean_ctor_get_uint8(v___x_824_, sizeof(void*)*4);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_824_, 0);
lean_dec(v_unused_921_);
v___x_830_ = v___x_824_;
v_isShared_831_ = v_isSharedCheck_920_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_hypotheses_827_);
lean_inc(v_target_826_);
lean_inc(v_typeAnalysis_825_);
lean_dec(v___x_824_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_920_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_preprocessCaches_809_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_preprocessCaches_809_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_typeAnalysis_825_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_target_826_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_hypotheses_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*4, v_didChange_828_);
v___x_833_ = v_reuseFailAlloc_919_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = lean_st_ref_put(v___x_823_, v___x_833_);
v_sz_835_ = lean_array_size(v_hypQueue_754_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_835_, v___x_836_, v_hypQueue_754_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_838_, v___x_795_, v___x_823_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v___x_795_);
lean_dec_ref_known(v___x_838_, 1);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_910_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_910_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_910_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_910_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_st_ref_get(v___x_823_);
lean_dec(v___x_823_);
v___x_845_ = lean_unbox(v_a_840_);
lean_dec(v_a_840_);
if (v___x_845_ == 0)
{
lean_object* v_caches_846_; lean_object* v_hypotheses_847_; lean_object* v___x_848_; lean_object* v_theoryState_849_; lean_object* v_satExpr_850_; lean_object* v_hypQueue_851_; lean_object* v_usedHyps_852_; uint8_t v_didChange_853_; lean_object* v_solverTimeBudgetMs_854_; lean_object* v_roundBudget_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_842_);
v_caches_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_caches_846_);
v_hypotheses_847_ = lean_ctor_get(v___x_844_, 3);
lean_inc_ref(v_hypotheses_847_);
lean_dec(v___x_844_);
v___x_848_ = lean_st_ref_take(v___y_756_);
v_theoryState_849_ = lean_ctor_get(v___x_848_, 3);
v_satExpr_850_ = lean_ctor_get(v___x_848_, 0);
v_hypQueue_851_ = lean_ctor_get(v___x_848_, 1);
v_usedHyps_852_ = lean_ctor_get(v___x_848_, 2);
v_didChange_853_ = lean_ctor_get_uint8(v___x_848_, sizeof(void*)*6);
v_solverTimeBudgetMs_854_ = lean_ctor_get(v___x_848_, 4);
v_roundBudget_855_ = lean_ctor_get(v___x_848_, 5);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_904_ == 0)
{
v___x_857_ = v___x_848_;
v_isShared_858_ = v_isSharedCheck_904_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_roundBudget_855_);
lean_inc(v_solverTimeBudgetMs_854_);
lean_inc(v_theoryState_849_);
lean_inc(v_usedHyps_852_);
lean_inc(v_hypQueue_851_);
lean_inc(v_satExpr_850_);
lean_dec(v___x_848_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_904_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_funState_859_; lean_object* v_bitvecState_860_; lean_object* v_satSolver_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_902_; 
v_funState_859_ = lean_ctor_get(v_theoryState_849_, 0);
v_bitvecState_860_ = lean_ctor_get(v_theoryState_849_, 1);
v_satSolver_861_ = lean_ctor_get(v_theoryState_849_, 3);
v_isSharedCheck_902_ = !lean_is_exclusive(v_theoryState_849_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_theoryState_849_, 2);
lean_dec(v_unused_903_);
v___x_863_ = v_theoryState_849_;
v_isShared_864_ = v_isSharedCheck_902_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_satSolver_861_);
lean_inc(v_bitvecState_860_);
lean_inc(v_funState_859_);
lean_dec(v_theoryState_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_902_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 2, v_caches_846_);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_funState_859_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_bitvecState_860_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_caches_846_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_satSolver_861_);
v___x_866_ = v_reuseFailAlloc_901_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 3, v___x_866_);
v___x_868_ = v___x_857_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_satExpr_850_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_hypQueue_851_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_usedHyps_852_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v_solverTimeBudgetMs_854_);
lean_ctor_set(v_reuseFailAlloc_900_, 5, v_roundBudget_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*6, v_didChange_853_);
v___x_868_ = v_reuseFailAlloc_900_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; size_t v_sz_870_; lean_object* v___x_871_; 
v___x_869_ = lean_st_ref_put(v___y_756_, v___x_868_);
v_sz_870_ = lean_array_size(v_hypotheses_847_);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_847_, v_sz_870_, v___x_836_, v___x_821_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v_hypotheses_847_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_891_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_891_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_891_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_891_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_array_get_size(v_a_872_);
v___x_877_ = lean_nat_dec_eq(v___x_876_, v___x_770_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v_satExpr_879_; uint8_t v___x_880_; 
lean_del_object(v___x_874_);
v___x_878_ = lean_st_ref_get(v___y_756_);
v_satExpr_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc_ref(v_satExpr_879_);
lean_dec(v___x_878_);
v___x_880_ = lean_nat_dec_lt(v___x_770_, v___x_876_);
if (v___x_880_ == 0)
{
lean_dec(v_a_872_);
v___y_720_ = v___y_756_;
v_a_721_ = v_satExpr_879_;
goto v___jp_719_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_le(v___x_876_, v___x_876_);
if (v___x_881_ == 0)
{
if (v___x_880_ == 0)
{
lean_dec(v_a_872_);
v___y_720_ = v___y_756_;
v_a_721_ = v_satExpr_879_;
goto v___jp_719_;
}
else
{
size_t v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_usize_of_nat(v___x_876_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_872_, v___x_836_, v___x_882_, v_satExpr_879_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v_a_872_);
v___y_742_ = v___y_756_;
v___y_743_ = v___x_883_;
goto v___jp_741_;
}
}
else
{
size_t v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_usize_of_nat(v___x_876_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_872_, v___x_836_, v___x_884_, v_satExpr_879_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v_a_872_);
v___y_742_ = v___y_756_;
v___y_743_ = v___x_885_;
goto v___jp_741_;
}
}
}
else
{
uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_a_872_);
v___x_886_ = 2;
v___x_887_ = lean_box(v___x_886_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_887_);
v___x_889_ = v___x_874_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_871_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_871_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
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
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_dec(v___x_844_);
v___x_905_ = 0;
v___x_906_ = lean_box(v___x_905_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_906_);
v___x_908_ = v___x_842_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v___x_823_);
v_a_911_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_839_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_839_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
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
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v_hypQueue_754_);
v___x_928_ = 2;
v___x_929_ = lean_box(v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1409_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1426_ = _args[0];
lean_object* v_msg_1427_ = _args[1];
lean_object* v___y_1428_ = _args[2];
lean_object* v___y_1429_ = _args[3];
lean_object* v___y_1430_ = _args[4];
lean_object* v___y_1431_ = _args[5];
lean_object* v___y_1432_ = _args[6];
lean_object* v___y_1433_ = _args[7];
lean_object* v___y_1434_ = _args[8];
lean_object* v___y_1435_ = _args[9];
lean_object* v___y_1436_ = _args[10];
lean_object* v___y_1437_ = _args[11];
lean_object* v___y_1438_ = _args[12];
lean_object* v___y_1439_ = _args[13];
lean_object* v___y_1440_ = _args[14];
lean_object* v___y_1441_ = _args[15];
lean_object* v___y_1442_ = _args[16];
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1426_, v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_1444_, size_t v_i_1445_, size_t v_stop_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_1444_, v_i_1445_, v_stop_1446_, v_b_1447_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object** _args){
lean_object* v_as_1464_ = _args[0];
lean_object* v_i_1465_ = _args[1];
lean_object* v_stop_1466_ = _args[2];
lean_object* v_b_1467_ = _args[3];
lean_object* v___y_1468_ = _args[4];
lean_object* v___y_1469_ = _args[5];
lean_object* v___y_1470_ = _args[6];
lean_object* v___y_1471_ = _args[7];
lean_object* v___y_1472_ = _args[8];
lean_object* v___y_1473_ = _args[9];
lean_object* v___y_1474_ = _args[10];
lean_object* v___y_1475_ = _args[11];
lean_object* v___y_1476_ = _args[12];
lean_object* v___y_1477_ = _args[13];
lean_object* v___y_1478_ = _args[14];
lean_object* v___y_1479_ = _args[15];
lean_object* v___y_1480_ = _args[16];
lean_object* v___y_1481_ = _args[17];
lean_object* v___y_1482_ = _args[18];
_start:
{
size_t v_i_boxed_1483_; size_t v_stop_boxed_1484_; lean_object* v_res_1485_; 
v_i_boxed_1483_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_stop_boxed_1484_ = lean_unbox_usize(v_stop_1466_);
lean_dec(v_stop_1466_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1464_, v_i_boxed_1483_, v_stop_boxed_1484_, v_b_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_as_1464_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object* v_00_u03b1_1486_, lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_1487_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1504_ = _args[0];
lean_object* v_x_1505_ = _args[1];
lean_object* v___y_1506_ = _args[2];
lean_object* v___y_1507_ = _args[3];
lean_object* v___y_1508_ = _args[4];
lean_object* v___y_1509_ = _args[5];
lean_object* v___y_1510_ = _args[6];
lean_object* v___y_1511_ = _args[7];
lean_object* v___y_1512_ = _args[8];
lean_object* v___y_1513_ = _args[9];
lean_object* v___y_1514_ = _args[10];
lean_object* v___y_1515_ = _args[11];
lean_object* v___y_1516_ = _args[12];
lean_object* v___y_1517_ = _args[13];
lean_object* v___y_1518_ = _args[14];
lean_object* v___y_1519_ = _args[15];
lean_object* v___y_1520_ = _args[16];
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(v_00_u03b1_1504_, v_x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object* v_oldTraces_1522_, lean_object* v_data_1523_, lean_object* v_ref_1524_, lean_object* v_msg_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_1522_, v_data_1523_, v_ref_1524_, v_msg_1525_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object** _args){
lean_object* v_oldTraces_1542_ = _args[0];
lean_object* v_data_1543_ = _args[1];
lean_object* v_ref_1544_ = _args[2];
lean_object* v_msg_1545_ = _args[3];
lean_object* v___y_1546_ = _args[4];
lean_object* v___y_1547_ = _args[5];
lean_object* v___y_1548_ = _args[6];
lean_object* v___y_1549_ = _args[7];
lean_object* v___y_1550_ = _args[8];
lean_object* v___y_1551_ = _args[9];
lean_object* v___y_1552_ = _args[10];
lean_object* v___y_1553_ = _args[11];
lean_object* v___y_1554_ = _args[12];
lean_object* v___y_1555_ = _args[13];
lean_object* v___y_1556_ = _args[14];
lean_object* v___y_1557_ = _args[15];
lean_object* v___y_1558_ = _args[16];
lean_object* v___y_1559_ = _args[17];
lean_object* v___y_1560_ = _args[18];
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1542_, v_data_1543_, v_ref_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1561_;
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

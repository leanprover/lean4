// Lean compiler output
// Module: Lean.Language.Util
// Imports: public import Lean.Elab.InfoTree import Init.Data.Format.Macro
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
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* lean_io_get_num_heartbeats();
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "\n• "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snapshotTree"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(11, 136, 72, 78, 187, 126, 217, 153)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 108, 214, 181, 226, 69, 54, 12)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value;
static lean_once_cell_t l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "<range inherited> "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<no range> "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(32u);
v___x_2_ = lean_mk_empty_array_with_capacity(v___x_1_);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((size_t)5ULL);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_unsigned_to_nat(32u);
v___x_7_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_8_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__0);
v___x_9_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_5_);
lean_ctor_set(v___x_9_, 3, v___x_5_);
lean_ctor_set_usize(v___x_9_, 4, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v_traceState_13_; lean_object* v_traces_14_; lean_object* v___x_15_; lean_object* v_traceState_16_; lean_object* v_env_17_; lean_object* v_nextMacroScope_18_; lean_object* v_ngen_19_; lean_object* v_auxDeclNGen_20_; lean_object* v_cache_21_; lean_object* v_recordedDeps_22_; lean_object* v_messages_23_; lean_object* v_infoState_24_; lean_object* v_snapshotTasks_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_44_; 
v___x_12_ = lean_st_ref_get(v___y_10_);
v_traceState_13_ = lean_ctor_get(v___x_12_, 4);
lean_inc_ref(v_traceState_13_);
lean_dec(v___x_12_);
v_traces_14_ = lean_ctor_get(v_traceState_13_, 0);
lean_inc_ref(v_traces_14_);
lean_dec_ref(v_traceState_13_);
v___x_15_ = lean_st_ref_take(v___y_10_);
v_traceState_16_ = lean_ctor_get(v___x_15_, 4);
v_env_17_ = lean_ctor_get(v___x_15_, 0);
v_nextMacroScope_18_ = lean_ctor_get(v___x_15_, 1);
v_ngen_19_ = lean_ctor_get(v___x_15_, 2);
v_auxDeclNGen_20_ = lean_ctor_get(v___x_15_, 3);
v_cache_21_ = lean_ctor_get(v___x_15_, 5);
v_recordedDeps_22_ = lean_ctor_get(v___x_15_, 6);
v_messages_23_ = lean_ctor_get(v___x_15_, 7);
v_infoState_24_ = lean_ctor_get(v___x_15_, 8);
v_snapshotTasks_25_ = lean_ctor_get(v___x_15_, 9);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_44_ == 0)
{
v___x_27_ = v___x_15_;
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_snapshotTasks_25_);
lean_inc(v_infoState_24_);
lean_inc(v_messages_23_);
lean_inc(v_recordedDeps_22_);
lean_inc(v_cache_21_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_20_);
lean_inc(v_ngen_19_);
lean_inc(v_nextMacroScope_18_);
lean_inc(v_env_17_);
lean_dec(v___x_15_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
uint64_t v_tid_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_42_; 
v_tid_29_ = lean_ctor_get_uint64(v_traceState_16_, sizeof(void*)*1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_traceState_16_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v_traceState_16_, 0);
lean_dec(v_unused_43_);
v___x_31_ = v_traceState_16_;
v_isShared_32_ = v_isSharedCheck_42_;
goto v_resetjp_30_;
}
else
{
lean_dec(v_traceState_16_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_42_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_33_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_33_);
lean_ctor_set_uint64(v_reuseFailAlloc_41_, sizeof(void*)*1, v_tid_29_);
v___x_35_ = v_reuseFailAlloc_41_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 4, v___x_35_);
v___x_37_ = v___x_27_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_env_17_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_nextMacroScope_18_);
lean_ctor_set(v_reuseFailAlloc_40_, 2, v_ngen_19_);
lean_ctor_set(v_reuseFailAlloc_40_, 3, v_auxDeclNGen_20_);
lean_ctor_set(v_reuseFailAlloc_40_, 4, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_40_, 5, v_cache_21_);
lean_ctor_set(v_reuseFailAlloc_40_, 6, v_recordedDeps_22_);
lean_ctor_set(v_reuseFailAlloc_40_, 7, v_messages_23_);
lean_ctor_set(v_reuseFailAlloc_40_, 8, v_infoState_24_);
lean_ctor_set(v_reuseFailAlloc_40_, 9, v_snapshotTasks_25_);
v___x_37_ = v_reuseFailAlloc_40_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_st_ref_put(v___y_10_, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v_traces_14_);
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___boxed(lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_45_);
lean_dec(v___y_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_55_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object* v_opts_56_, lean_object* v_opt_57_){
_start:
{
lean_object* v_name_58_; lean_object* v_defValue_59_; lean_object* v_map_60_; lean_object* v___x_61_; 
v_name_58_ = lean_ctor_get(v_opt_57_, 0);
v_defValue_59_ = lean_ctor_get(v_opt_57_, 1);
v_map_60_ = lean_ctor_get(v_opts_56_, 0);
v___x_61_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_60_, v_name_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
uint8_t v___x_62_; 
v___x_62_ = lean_unbox(v_defValue_59_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; 
v_val_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___x_61_, 1);
if (lean_obj_tag(v_val_63_) == 1)
{
uint8_t v_v_64_; 
v_v_64_ = lean_ctor_get_uint8(v_val_63_, 0);
lean_dec_ref_known(v_val_63_, 0);
return v_v_64_;
}
else
{
uint8_t v___x_65_; 
lean_dec(v_val_63_);
v___x_65_ = lean_unbox(v_defValue_59_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object* v_opts_66_, lean_object* v_opt_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_66_, v_opt_67_);
lean_dec_ref(v_opt_67_);
lean_dec_ref(v_opts_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object* v___x_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = l_Lean_MessageData_ofFormat(v___x_70_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object* v___x_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(v___x_77_, v_x_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec_ref(v_x_78_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_83_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
lean_ctor_set(v___x_89_, 3, v___x_88_);
lean_ctor_set(v___x_89_, 4, v___x_87_);
lean_ctor_set(v___x_89_, 5, v___x_87_);
lean_ctor_set(v___x_89_, 6, v___x_87_);
lean_ctor_set(v___x_89_, 7, v___x_87_);
lean_ctor_set(v___x_89_, 8, v___x_87_);
lean_ctor_set(v___x_89_, 9, v___x_87_);
lean_ctor_set(v___x_89_, 10, v___x_87_);
lean_ctor_set(v___x_89_, 11, v___x_86_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(32u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
v___x_98_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_94_);
lean_ctor_set(v___x_98_, 3, v___x_94_);
lean_ctor_set_usize(v___x_98_, 4, v___x_93_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_box(1);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
v___x_101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_toCold_108_; lean_object* v_env_109_; lean_object* v_options_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_toCold_108_ = lean_ctor_get(v___y_104_, 0);
v_env_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_107_);
v_options_110_ = lean_ctor_get(v_toCold_108_, 2);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_109_, v___x_111_);
v___x_113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_110_);
v___x_115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_115_, 0, v_env_112_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
lean_ctor_set(v___x_115_, 3, v_options_110_);
v___x_116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_msgData_103_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_122_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_123_; double v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_float_of_nat(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_128_, lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_ref_133_; lean_object* v___x_134_; lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_180_; 
v_ref_133_ = lean_ctor_get(v___y_130_, 2);
v___x_134_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_129_, v___y_130_, v___y_131_);
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_180_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_180_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_180_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v_traceState_140_; lean_object* v_env_141_; lean_object* v_nextMacroScope_142_; lean_object* v_ngen_143_; lean_object* v_auxDeclNGen_144_; lean_object* v_cache_145_; lean_object* v_recordedDeps_146_; lean_object* v_messages_147_; lean_object* v_infoState_148_; lean_object* v_snapshotTasks_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_179_; 
v___x_139_ = lean_st_ref_take(v___y_131_);
v_traceState_140_ = lean_ctor_get(v___x_139_, 4);
v_env_141_ = lean_ctor_get(v___x_139_, 0);
v_nextMacroScope_142_ = lean_ctor_get(v___x_139_, 1);
v_ngen_143_ = lean_ctor_get(v___x_139_, 2);
v_auxDeclNGen_144_ = lean_ctor_get(v___x_139_, 3);
v_cache_145_ = lean_ctor_get(v___x_139_, 5);
v_recordedDeps_146_ = lean_ctor_get(v___x_139_, 6);
v_messages_147_ = lean_ctor_get(v___x_139_, 7);
v_infoState_148_ = lean_ctor_get(v___x_139_, 8);
v_snapshotTasks_149_ = lean_ctor_get(v___x_139_, 9);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_179_ == 0)
{
v___x_151_ = v___x_139_;
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_snapshotTasks_149_);
lean_inc(v_infoState_148_);
lean_inc(v_messages_147_);
lean_inc(v_recordedDeps_146_);
lean_inc(v_cache_145_);
lean_inc(v_traceState_140_);
lean_inc(v_auxDeclNGen_144_);
lean_inc(v_ngen_143_);
lean_inc(v_nextMacroScope_142_);
lean_inc(v_env_141_);
lean_dec(v___x_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint64_t v_tid_153_; lean_object* v_traces_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_178_; 
v_tid_153_ = lean_ctor_get_uint64(v_traceState_140_, sizeof(void*)*1);
v_traces_154_ = lean_ctor_get(v_traceState_140_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_traceState_140_);
if (v_isSharedCheck_178_ == 0)
{
v___x_156_ = v_traceState_140_;
v_isShared_157_ = v_isSharedCheck_178_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_traces_154_);
lean_dec(v_traceState_140_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_178_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; double v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_box(0);
v___x_160_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_161_ = 0;
v___x_162_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_163_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_163_, 0, v_cls_128_);
lean_ctor_set(v___x_163_, 1, v___x_159_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
lean_ctor_set_float(v___x_163_, sizeof(void*)*3, v___x_160_);
lean_ctor_set_float(v___x_163_, sizeof(void*)*3 + 8, v___x_160_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*3 + 16, v___x_161_);
v___x_164_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_165_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v_a_135_);
lean_ctor_set(v___x_165_, 2, v___x_164_);
lean_inc(v_ref_133_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_ref_133_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_PersistentArray_push___redArg(v_traces_154_, v___x_166_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_167_);
v___x_169_ = v___x_156_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_167_);
lean_ctor_set_uint64(v_reuseFailAlloc_177_, sizeof(void*)*1, v_tid_153_);
v___x_169_ = v_reuseFailAlloc_177_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_169_);
v___x_171_ = v___x_151_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_env_141_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_nextMacroScope_142_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_ngen_143_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_auxDeclNGen_144_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v_cache_145_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_recordedDeps_146_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_messages_147_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_infoState_148_);
lean_ctor_set(v_reuseFailAlloc_176_, 9, v_snapshotTasks_149_);
v___x_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_st_ref_put(v___y_131_, v___x_171_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_158_);
v___x_174_ = v___x_137_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_158_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_181_, v_msg_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_dec(v_pre_187_);
return v_x_188_;
}
else
{
lean_object* v_head_190_; lean_object* v_tail_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v_head_190_ = lean_ctor_get(v_x_189_, 0);
v_tail_191_ = lean_ctor_get(v_x_189_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v_x_189_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_tail_191_);
lean_inc(v_head_190_);
lean_dec(v_x_189_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
lean_inc(v_pre_187_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 5);
lean_ctor_set(v___x_193_, 1, v_pre_187_);
lean_ctor_set(v___x_193_, 0, v_x_188_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_x_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_pre_187_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v_head_190_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v_x_188_ = v___x_198_;
v_x_189_ = v_tail_191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_204_; 
lean_dec(v_pre_202_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_head_205_; lean_object* v_tail_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_head_205_ = lean_ctor_get(v_x_203_, 0);
v_tail_206_ = lean_ctor_get(v_x_203_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_tail_206_);
lean_inc(v_head_205_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v_head_205_);
lean_inc(v_pre_202_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 5);
lean_ctor_set(v___x_208_, 1, v___x_210_);
lean_ctor_set(v___x_208_, 0, v_pre_202_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_pre_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_202_, v___x_212_, v_tail_206_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_List_reverse___redArg(v_x_217_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v_head_221_ = lean_ctor_get(v_x_216_, 0);
v_tail_222_ = lean_ctor_get(v_x_216_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_232_ == 0)
{
v___x_224_ = v_x_216_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_x_216_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = 0;
v___x_227_ = l_Lean_Message_toString(v_head_221_, v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_x_217_);
lean_ctor_set(v___x_224_, 0, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_x_217_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v_x_216_ = v_tail_222_;
v_x_217_ = v___x_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_233_, v_x_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v_x_237_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v_x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v_x_237_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v_x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 0);
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_258_, lean_object* v_opt_259_){
_start:
{
lean_object* v_name_260_; lean_object* v_defValue_261_; lean_object* v_map_262_; lean_object* v___x_263_; 
v_name_260_ = lean_ctor_get(v_opt_259_, 0);
v_defValue_261_ = lean_ctor_get(v_opt_259_, 1);
v_map_262_ = lean_ctor_get(v_opts_258_, 0);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_262_, v_name_260_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_inc(v_defValue_261_);
return v_defValue_261_;
}
else
{
lean_object* v_val_264_; 
v_val_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_263_, 1);
if (lean_obj_tag(v_val_264_) == 3)
{
lean_object* v_v_265_; 
v_v_265_ = lean_ctor_get(v_val_264_, 0);
lean_inc(v_v_265_);
lean_dec_ref_known(v_val_264_, 1);
return v_v_265_;
}
else
{
lean_dec(v_val_264_);
lean_inc(v_defValue_261_);
return v_defValue_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_266_, v_opt_267_);
lean_dec_ref(v_opt_267_);
lean_dec_ref(v_opts_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_269_, size_t v_i_270_, lean_object* v_bs_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_lt(v_i_270_, v_sz_269_);
if (v___x_272_ == 0)
{
return v_bs_271_;
}
else
{
lean_object* v_v_273_; lean_object* v_msg_274_; lean_object* v___x_275_; lean_object* v_bs_x27_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_v_273_ = lean_array_uget_borrowed(v_bs_271_, v_i_270_);
v_msg_274_ = lean_ctor_get(v_v_273_, 1);
lean_inc_ref(v_msg_274_);
v___x_275_ = lean_unsigned_to_nat(0u);
v_bs_x27_276_ = lean_array_uset(v_bs_271_, v_i_270_, v___x_275_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_270_, v___x_277_);
v___x_279_ = lean_array_uset(v_bs_x27_276_, v_i_270_, v_msg_274_);
v_i_270_ = v___x_278_;
v_bs_271_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_281_, lean_object* v_i_282_, lean_object* v_bs_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_281_);
lean_dec(v_sz_281_);
v_i_boxed_285_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_284_, v_i_boxed_285_, v_bs_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_287_, lean_object* v_data_288_, lean_object* v_ref_289_, lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_toCold_294_; lean_object* v_currRecDepth_295_; lean_object* v_ref_296_; uint16_t v_optionFlags_297_; uint8_t v_suppressElabErrors_298_; uint8_t v_checkDeprecated_299_; uint8_t v_isRecordingDeps_300_; lean_object* v_ref_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_traceState_304_; lean_object* v_traces_305_; lean_object* v___x_306_; size_t v_sz_307_; size_t v___x_308_; lean_object* v___x_309_; lean_object* v_msg_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_350_; 
v_toCold_294_ = lean_ctor_get(v___y_291_, 0);
v_currRecDepth_295_ = lean_ctor_get(v___y_291_, 1);
v_ref_296_ = lean_ctor_get(v___y_291_, 2);
v_optionFlags_297_ = lean_ctor_get_uint16(v___y_291_, sizeof(void*)*3);
v_suppressElabErrors_298_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 2);
v_checkDeprecated_299_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 3);
v_isRecordingDeps_300_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 4);
v_ref_301_ = l_Lean_replaceRef(v_ref_289_, v_ref_296_);
lean_inc(v_currRecDepth_295_);
lean_inc_ref(v_toCold_294_);
v___x_302_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_302_, 0, v_toCold_294_);
lean_ctor_set(v___x_302_, 1, v_currRecDepth_295_);
lean_ctor_set(v___x_302_, 2, v_ref_301_);
lean_ctor_set_uint16(v___x_302_, sizeof(void*)*3, v_optionFlags_297_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*3 + 2, v_suppressElabErrors_298_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*3 + 3, v_checkDeprecated_299_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*3 + 4, v_isRecordingDeps_300_);
v___x_303_ = lean_st_ref_get(v___y_292_);
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
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_307_, v___x_308_, v___x_306_);
v_msg_310_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_310_, 0, v_data_288_);
lean_ctor_set(v_msg_310_, 1, v_msg_290_);
lean_ctor_set(v_msg_310_, 2, v___x_309_);
v___x_311_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_310_, v___x_302_, v___y_292_);
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
v___x_316_ = lean_st_ref_take(v___y_292_);
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
lean_ctor_set(v___x_335_, 0, v_ref_289_);
lean_ctor_set(v___x_335_, 1, v_a_312_);
v___x_336_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_287_, v___x_335_);
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
v___x_341_ = lean_st_ref_put(v___y_292_, v___x_340_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_351_, lean_object* v_data_352_, lean_object* v_ref_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_351_, v_data_352_, v_ref_353_, v_msg_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_359_){
_start:
{
if (lean_obj_tag(v_e_359_) == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 2;
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_362_);
lean_dec_ref(v_e_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_368_; double v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(1000u);
v___x_369_ = lean_float_of_nat(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_370_, uint8_t v_collapsed_371_, lean_object* v_tag_372_, lean_object* v_opts_373_, uint8_t v_clsEnabled_374_, lean_object* v_oldTraces_375_, lean_object* v_msg_376_, lean_object* v_resStartStop_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v_data_386_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___y_394_; lean_object* v_a_395_; uint8_t v___y_410_; double v___y_442_; 
v_fst_381_ = lean_ctor_get(v_resStartStop_377_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v_resStartStop_377_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v_resStartStop_377_);
v_fst_389_ = lean_ctor_get(v_snd_382_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_snd_382_, 1);
lean_inc(v_snd_390_);
lean_dec(v_snd_382_);
v___x_391_ = l_Lean_trace_profiler;
v___x_392_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_373_, v___x_391_);
if (v___x_392_ == 0)
{
v___y_410_ = v___x_392_;
goto v___jp_409_;
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = l_Lean_trace_profiler_useHeartbeats;
v___x_448_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_373_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; double v___x_451_; double v___x_452_; double v___x_453_; 
v___x_449_ = l_Lean_trace_profiler_threshold;
v___x_450_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_373_, v___x_449_);
v___x_451_ = lean_float_of_nat(v___x_450_);
v___x_452_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_453_ = lean_float_div(v___x_451_, v___x_452_);
v___y_442_ = v___x_453_;
goto v___jp_441_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; double v___x_456_; 
v___x_454_ = l_Lean_trace_profiler_threshold;
v___x_455_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_373_, v___x_454_);
v___x_456_ = lean_float_of_nat(v___x_455_);
v___y_442_ = v___x_456_;
goto v___jp_441_;
}
}
v___jp_383_:
{
lean_object* v___x_387_; 
lean_inc(v___y_385_);
v___x_387_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_375_, v_data_386_, v___y_385_, v___y_384_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
lean_dec_ref_known(v___x_387_, 1);
v___x_388_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_381_);
return v___x_388_;
}
else
{
lean_dec(v_fst_381_);
return v___x_387_;
}
}
v___jp_393_:
{
uint8_t v_result_396_; lean_object* v___x_397_; lean_object* v___x_398_; double v___x_399_; lean_object* v_data_400_; 
v_result_396_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_381_);
v___x_397_ = lean_box(v_result_396_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_372_);
lean_inc_ref(v___x_398_);
lean_inc(v_cls_370_);
v_data_400_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_400_, 0, v_cls_370_);
lean_ctor_set(v_data_400_, 1, v___x_398_);
lean_ctor_set(v_data_400_, 2, v_tag_372_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3, v___x_399_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3 + 8, v___x_399_);
lean_ctor_set_uint8(v_data_400_, sizeof(void*)*3 + 16, v_collapsed_371_);
if (v___x_392_ == 0)
{
lean_dec_ref_known(v___x_398_, 1);
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
lean_dec_ref(v_tag_372_);
lean_dec(v_cls_370_);
v___y_384_ = v_a_395_;
v___y_385_ = v___y_394_;
v_data_386_ = v_data_400_;
goto v___jp_383_;
}
else
{
lean_object* v_data_401_; double v___x_402_; double v___x_403_; 
lean_dec_ref_known(v_data_400_, 3);
v_data_401_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_401_, 0, v_cls_370_);
lean_ctor_set(v_data_401_, 1, v___x_398_);
lean_ctor_set(v_data_401_, 2, v_tag_372_);
v___x_402_ = lean_unbox_float(v_fst_389_);
lean_dec(v_fst_389_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3, v___x_402_);
v___x_403_ = lean_unbox_float(v_snd_390_);
lean_dec(v_snd_390_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3 + 8, v___x_403_);
lean_ctor_set_uint8(v_data_401_, sizeof(void*)*3 + 16, v_collapsed_371_);
v___y_384_ = v_a_395_;
v___y_385_ = v___y_394_;
v_data_386_ = v_data_401_;
goto v___jp_383_;
}
}
v___jp_404_:
{
lean_object* v_ref_405_; lean_object* v___x_406_; 
v_ref_405_ = lean_ctor_get(v___y_378_, 2);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
lean_inc(v_fst_381_);
v___x_406_ = lean_apply_4(v_msg_376_, v_fst_381_, v___y_378_, v___y_379_, lean_box(0));
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___y_394_ = v_ref_405_;
v_a_395_ = v_a_407_;
goto v___jp_393_;
}
else
{
lean_object* v___x_408_; 
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_394_ = v_ref_405_;
v_a_395_ = v___x_408_;
goto v___jp_393_;
}
}
v___jp_409_:
{
if (v_clsEnabled_374_ == 0)
{
if (v___y_410_ == 0)
{
lean_object* v___x_411_; lean_object* v_traceState_412_; lean_object* v_env_413_; lean_object* v_nextMacroScope_414_; lean_object* v_ngen_415_; lean_object* v_auxDeclNGen_416_; lean_object* v_cache_417_; lean_object* v_recordedDeps_418_; lean_object* v_messages_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
lean_dec_ref(v_msg_376_);
lean_dec_ref(v_tag_372_);
lean_dec(v_cls_370_);
v___x_411_ = lean_st_ref_take(v___y_379_);
v_traceState_412_ = lean_ctor_get(v___x_411_, 4);
v_env_413_ = lean_ctor_get(v___x_411_, 0);
v_nextMacroScope_414_ = lean_ctor_get(v___x_411_, 1);
v_ngen_415_ = lean_ctor_get(v___x_411_, 2);
v_auxDeclNGen_416_ = lean_ctor_get(v___x_411_, 3);
v_cache_417_ = lean_ctor_get(v___x_411_, 5);
v_recordedDeps_418_ = lean_ctor_get(v___x_411_, 6);
v_messages_419_ = lean_ctor_get(v___x_411_, 7);
v_infoState_420_ = lean_ctor_get(v___x_411_, 8);
v_snapshotTasks_421_ = lean_ctor_get(v___x_411_, 9);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_440_ == 0)
{
v___x_423_ = v___x_411_;
v_isShared_424_ = v_isSharedCheck_440_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_messages_419_);
lean_inc(v_recordedDeps_418_);
lean_inc(v_cache_417_);
lean_inc(v_traceState_412_);
lean_inc(v_auxDeclNGen_416_);
lean_inc(v_ngen_415_);
lean_inc(v_nextMacroScope_414_);
lean_inc(v_env_413_);
lean_dec(v___x_411_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_440_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint64_t v_tid_425_; lean_object* v_traces_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_439_; 
v_tid_425_ = lean_ctor_get_uint64(v_traceState_412_, sizeof(void*)*1);
v_traces_426_ = lean_ctor_get(v_traceState_412_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_traceState_412_);
if (v_isSharedCheck_439_ == 0)
{
v___x_428_ = v_traceState_412_;
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_traces_426_);
lean_dec(v_traceState_412_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_375_, v_traces_426_);
lean_dec_ref(v_traces_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_430_);
lean_ctor_set_uint64(v_reuseFailAlloc_438_, sizeof(void*)*1, v_tid_425_);
v___x_432_ = v_reuseFailAlloc_438_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v___x_432_);
v___x_434_ = v___x_423_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_env_413_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_nextMacroScope_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_ngen_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_auxDeclNGen_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_recordedDeps_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_messages_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_snapshotTasks_421_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_ref_put(v___y_379_, v___x_434_);
v___x_436_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_381_);
return v___x_436_;
}
}
}
}
}
else
{
goto v___jp_404_;
}
}
else
{
goto v___jp_404_;
}
}
v___jp_441_:
{
double v___x_443_; double v___x_444_; double v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unbox_float(v_snd_390_);
v___x_444_ = lean_unbox_float(v_fst_389_);
v___x_445_ = lean_float_sub(v___x_443_, v___x_444_);
v___x_446_ = lean_float_decLt(v___y_442_, v___x_445_);
v___y_410_ = v___x_446_;
goto v___jp_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_457_, lean_object* v_collapsed_458_, lean_object* v_tag_459_, lean_object* v_opts_460_, lean_object* v_clsEnabled_461_, lean_object* v_oldTraces_462_, lean_object* v_msg_463_, lean_object* v_resStartStop_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v_collapsed_boxed_468_; uint8_t v_clsEnabled_boxed_469_; lean_object* v_res_470_; 
v_collapsed_boxed_468_ = lean_unbox(v_collapsed_458_);
v_clsEnabled_boxed_469_ = lean_unbox(v_clsEnabled_461_);
v_res_470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_457_, v_collapsed_boxed_468_, v_tag_459_, v_opts_460_, v_clsEnabled_boxed_469_, v_oldTraces_462_, v_msg_463_, v_resStartStop_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec_ref(v_opts_460_);
return v_res_470_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_471_; double v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(1000000000u);
v___x_472_ = lean_float_of_nat(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_486_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_487_ = l_Lean_Name_append(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_492_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_493_ = l_Lean_Name_append(v___x_492_, v___x_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_515_, lean_object* v_s_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; lean_object* v_a_531_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; uint8_t v___y_549_; lean_object* v___y_550_; lean_object* v_a_551_; lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; lean_object* v_a_564_; lean_object* v___y_567_; uint8_t v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; uint8_t v___y_575_; lean_object* v___y_576_; lean_object* v_a_577_; uint8_t v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; lean_object* v_a_600_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v_a_613_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; uint8_t v___y_628_; lean_object* v_element_699_; lean_object* v_children_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_866_; 
v_element_699_ = lean_ctor_get(v_s_516_, 0);
v_children_700_ = lean_ctor_get(v_s_516_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_s_516_);
if (v_isSharedCheck_866_ == 0)
{
v___x_702_ = v_s_516_;
v_isShared_703_ = v_isSharedCheck_866_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_children_700_);
lean_inc(v_element_699_);
lean_dec(v_s_516_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_866_;
goto v_resetjp_701_;
}
v___jp_520_:
{
lean_object* v___x_532_; double v___x_533_; double v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_532_ = lean_io_get_num_heartbeats();
v___x_533_ = lean_float_of_nat(v___y_521_);
v___x_534_ = lean_float_of_nat(v___x_532_);
v___x_535_ = lean_box_float(v___x_533_);
v___x_536_ = lean_box_float(v___x_534_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_a_531_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_inc_ref(v___y_527_);
lean_inc(v___y_528_);
v___x_539_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_528_, v___y_523_, v___y_527_, v___y_525_, v___y_529_, v___y_530_, v___y_522_, v___x_538_, v___y_526_, v___y_524_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v_a_551_);
v___y_521_ = v___y_541_;
v___y_522_ = v___y_543_;
v___y_523_ = v___y_542_;
v___y_524_ = v___y_545_;
v___y_525_ = v___y_544_;
v___y_526_ = v___y_546_;
v___y_527_ = v___y_547_;
v___y_528_ = v___y_548_;
v___y_529_ = v___y_549_;
v___y_530_ = v___y_550_;
v_a_531_ = v___x_552_;
goto v___jp_520_;
}
v___jp_553_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_a_564_);
v___y_521_ = v___y_554_;
v___y_522_ = v___y_556_;
v___y_523_ = v___y_555_;
v___y_524_ = v___y_558_;
v___y_525_ = v___y_557_;
v___y_526_ = v___y_559_;
v___y_527_ = v___y_560_;
v___y_528_ = v___y_561_;
v___y_529_ = v___y_562_;
v___y_530_ = v___y_563_;
v_a_531_ = v___x_565_;
goto v___jp_520_;
}
v___jp_566_:
{
lean_object* v___x_578_; double v___x_579_; double v___x_580_; double v___x_581_; double v___x_582_; double v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_578_ = lean_io_mono_nanos_now();
v___x_579_ = lean_float_of_nat(v___y_571_);
v___x_580_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_581_ = lean_float_div(v___x_579_, v___x_580_);
v___x_582_ = lean_float_of_nat(v___x_578_);
v___x_583_ = lean_float_div(v___x_582_, v___x_580_);
v___x_584_ = lean_box_float(v___x_581_);
v___x_585_ = lean_box_float(v___x_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_a_577_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_574_);
v___x_588_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_574_, v___y_568_, v___y_573_, v___y_570_, v___y_575_, v___y_576_, v___y_567_, v___x_587_, v___y_572_, v___y_569_);
return v___x_588_;
}
v___jp_589_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_a_600_);
v___y_567_ = v___y_591_;
v___y_568_ = v___y_590_;
v___y_569_ = v___y_594_;
v___y_570_ = v___y_593_;
v___y_571_ = v___y_592_;
v___y_572_ = v___y_595_;
v___y_573_ = v___y_596_;
v___y_574_ = v___y_597_;
v___y_575_ = v___y_598_;
v___y_576_ = v___y_599_;
v_a_577_ = v___x_601_;
goto v___jp_566_;
}
v___jp_602_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_613_);
v___y_567_ = v___y_604_;
v___y_568_ = v___y_603_;
v___y_569_ = v___y_607_;
v___y_570_ = v___y_606_;
v___y_571_ = v___y_605_;
v___y_572_ = v___y_608_;
v___y_573_ = v___y_609_;
v___y_574_ = v___y_610_;
v___y_575_ = v___y_611_;
v___y_576_ = v___y_612_;
v_a_577_ = v___x_614_;
goto v___jp_566_;
}
v___jp_615_:
{
lean_object* v___x_629_; 
v___x_629_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_619_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_trace_profiler_useHeartbeats;
v___x_632_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_620_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_io_mono_nanos_now();
v___x_634_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_616_, v___y_621_, v___y_619_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref_known(v___x_634_, 1);
if (lean_obj_tag(v___y_625_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_val_635_ = lean_ctor_get(v___y_625_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___y_625_, 1);
v___x_636_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_622_);
v___x_637_ = l_Lean_Name_mkStr2(v___y_622_, v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_637_);
v___x_639_ = l_Lean_Name_append(v___x_638_, v___x_637_);
v___x_640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_617_, v___y_620_, v___x_639_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v___x_637_);
lean_dec(v_val_635_);
v___x_641_ = lean_box(0);
v___y_590_ = v___y_618_;
v___y_591_ = v___y_624_;
v___y_592_ = v___x_633_;
v___y_593_ = v___y_620_;
v___y_594_ = v___y_619_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_626_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_628_;
v___y_599_ = v_a_630_;
v_a_600_ = v___x_641_;
goto v___jp_589_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_box(0);
v___x_643_ = l_Lean_Elab_InfoTree_format(v_val_635_, v___x_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_MessageData_ofFormat(v_a_644_);
v___x_646_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_637_, v___x_645_, v___y_621_, v___y_619_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___y_590_ = v___y_618_;
v___y_591_ = v___y_624_;
v___y_592_ = v___x_633_;
v___y_593_ = v___y_620_;
v___y_594_ = v___y_619_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_626_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_628_;
v___y_599_ = v_a_630_;
v_a_600_ = v_a_647_;
goto v___jp_589_;
}
else
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_646_, 1);
v___y_603_ = v___y_618_;
v___y_604_ = v___y_624_;
v___y_605_ = v___x_633_;
v___y_606_ = v___y_620_;
v___y_607_ = v___y_619_;
v___y_608_ = v___y_621_;
v___y_609_ = v___y_626_;
v___y_610_ = v___y_627_;
v___y_611_ = v___y_628_;
v___y_612_ = v_a_630_;
v_a_613_ = v_a_648_;
goto v___jp_602_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_659_; 
lean_dec(v___x_637_);
v_a_649_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_659_ == 0)
{
v___x_651_ = v___x_643_;
v_isShared_652_ = v_isSharedCheck_659_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_643_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_659_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_io_error_to_string(v_a_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 3);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = l_Lean_MessageData_ofFormat(v___x_655_);
lean_inc(v___y_623_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_623_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___y_603_ = v___y_618_;
v___y_604_ = v___y_624_;
v___y_605_ = v___x_633_;
v___y_606_ = v___y_620_;
v___y_607_ = v___y_619_;
v___y_608_ = v___y_621_;
v___y_609_ = v___y_626_;
v___y_610_ = v___y_627_;
v___y_611_ = v___y_628_;
v___y_612_ = v_a_630_;
v_a_613_ = v___x_657_;
goto v___jp_602_;
}
}
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v___y_625_);
v___x_660_ = lean_box(0);
v___y_590_ = v___y_618_;
v___y_591_ = v___y_624_;
v___y_592_ = v___x_633_;
v___y_593_ = v___y_620_;
v___y_594_ = v___y_619_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_626_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_628_;
v___y_599_ = v_a_630_;
v_a_600_ = v___x_660_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_661_; 
lean_dec(v___y_625_);
v_a_661_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_634_, 1);
v___y_603_ = v___y_618_;
v___y_604_ = v___y_624_;
v___y_605_ = v___x_633_;
v___y_606_ = v___y_620_;
v___y_607_ = v___y_619_;
v___y_608_ = v___y_621_;
v___y_609_ = v___y_626_;
v___y_610_ = v___y_627_;
v___y_611_ = v___y_628_;
v___y_612_ = v_a_630_;
v_a_613_ = v_a_661_;
goto v___jp_602_;
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_io_get_num_heartbeats();
v___x_663_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_616_, v___y_621_, v___y_619_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
if (lean_obj_tag(v___y_625_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_val_664_ = lean_ctor_get(v___y_625_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___y_625_, 1);
v___x_665_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_622_);
v___x_666_ = l_Lean_Name_mkStr2(v___y_622_, v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_666_);
v___x_668_ = l_Lean_Name_append(v___x_667_, v___x_666_);
v___x_669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_617_, v___y_620_, v___x_668_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_666_);
lean_dec(v_val_664_);
v___x_670_ = lean_box(0);
v___y_541_ = v___x_662_;
v___y_542_ = v___y_618_;
v___y_543_ = v___y_624_;
v___y_544_ = v___y_620_;
v___y_545_ = v___y_619_;
v___y_546_ = v___y_621_;
v___y_547_ = v___y_626_;
v___y_548_ = v___y_627_;
v___y_549_ = v___y_628_;
v___y_550_ = v_a_630_;
v_a_551_ = v___x_670_;
goto v___jp_540_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_box(0);
v___x_672_ = l_Lean_Elab_InfoTree_format(v_val_664_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_MessageData_ofFormat(v_a_673_);
v___x_675_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_666_, v___x_674_, v___y_621_, v___y_619_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___y_541_ = v___x_662_;
v___y_542_ = v___y_618_;
v___y_543_ = v___y_624_;
v___y_544_ = v___y_620_;
v___y_545_ = v___y_619_;
v___y_546_ = v___y_621_;
v___y_547_ = v___y_626_;
v___y_548_ = v___y_627_;
v___y_549_ = v___y_628_;
v___y_550_ = v_a_630_;
v_a_551_ = v_a_676_;
goto v___jp_540_;
}
else
{
lean_object* v_a_677_; 
v_a_677_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_675_, 1);
v___y_554_ = v___x_662_;
v___y_555_ = v___y_618_;
v___y_556_ = v___y_624_;
v___y_557_ = v___y_620_;
v___y_558_ = v___y_619_;
v___y_559_ = v___y_621_;
v___y_560_ = v___y_626_;
v___y_561_ = v___y_627_;
v___y_562_ = v___y_628_;
v___y_563_ = v_a_630_;
v_a_564_ = v_a_677_;
goto v___jp_553_;
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
lean_dec(v___x_666_);
v_a_678_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_688_ == 0)
{
v___x_680_ = v___x_672_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_672_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_io_error_to_string(v_a_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 3);
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_687_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_MessageData_ofFormat(v___x_684_);
lean_inc(v___y_623_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___y_623_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___y_554_ = v___x_662_;
v___y_555_ = v___y_618_;
v___y_556_ = v___y_624_;
v___y_557_ = v___y_620_;
v___y_558_ = v___y_619_;
v___y_559_ = v___y_621_;
v___y_560_ = v___y_626_;
v___y_561_ = v___y_627_;
v___y_562_ = v___y_628_;
v___y_563_ = v_a_630_;
v_a_564_ = v___x_686_;
goto v___jp_553_;
}
}
}
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v___y_625_);
v___x_689_ = lean_box(0);
v___y_541_ = v___x_662_;
v___y_542_ = v___y_618_;
v___y_543_ = v___y_624_;
v___y_544_ = v___y_620_;
v___y_545_ = v___y_619_;
v___y_546_ = v___y_621_;
v___y_547_ = v___y_626_;
v___y_548_ = v___y_627_;
v___y_549_ = v___y_628_;
v___y_550_ = v_a_630_;
v_a_551_ = v___x_689_;
goto v___jp_540_;
}
}
else
{
lean_object* v_a_690_; 
lean_dec(v___y_625_);
v_a_690_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_663_, 1);
v___y_554_ = v___x_662_;
v___y_555_ = v___y_618_;
v___y_556_ = v___y_624_;
v___y_557_ = v___y_620_;
v___y_558_ = v___y_619_;
v___y_559_ = v___y_621_;
v___y_560_ = v___y_626_;
v___y_561_ = v___y_627_;
v___y_562_ = v___y_628_;
v___y_563_ = v_a_630_;
v_a_564_ = v_a_690_;
goto v___jp_553_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_616_);
v_a_691_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_629_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_629_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
v_resetjp_701_:
{
lean_object* v_desc_704_; lean_object* v_diagnostics_705_; lean_object* v_infoTree_x3f_706_; lean_object* v_desc_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___x_801_; 
v_desc_704_ = lean_ctor_get(v_element_699_, 0);
lean_inc_ref(v_desc_704_);
v_diagnostics_705_ = lean_ctor_get(v_element_699_, 1);
lean_inc_ref(v_diagnostics_705_);
v_infoTree_x3f_706_ = lean_ctor_get(v_element_699_, 2);
lean_inc(v_infoTree_x3f_706_);
lean_dec_ref(v_element_699_);
v___x_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_801_, 0, v_desc_704_);
switch(lean_obj_tag(v_range_x3f_515_))
{
case 0:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v_desc_708_ = v___x_803_;
v___y_709_ = v_a_517_;
v___y_710_ = v_a_518_;
goto v___jp_707_;
}
case 1:
{
lean_object* v_toCold_804_; lean_object* v_range_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_863_; 
v_toCold_804_ = lean_ctor_get(v_a_517_, 0);
v_range_805_ = lean_ctor_get(v_range_x3f_515_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_range_x3f_515_);
if (v_isSharedCheck_863_ == 0)
{
v___x_807_ = v_range_x3f_515_;
v_isShared_808_ = v_isSharedCheck_863_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_range_805_);
lean_dec(v_range_x3f_515_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_863_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_fileMap_809_; lean_object* v_start_810_; lean_object* v_stop_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_862_; 
v_fileMap_809_ = lean_ctor_get(v_toCold_804_, 1);
v_start_810_ = lean_ctor_get(v_range_805_, 0);
v_stop_811_ = lean_ctor_get(v_range_805_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_range_805_);
if (v_isSharedCheck_862_ == 0)
{
v___x_813_ = v_range_805_;
v_isShared_814_ = v_isSharedCheck_862_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_stop_811_);
lean_inc(v_start_810_);
lean_dec(v_range_805_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_862_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v_line_816_; lean_object* v_column_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_fileMap_809_);
v___x_815_ = l_Lean_FileMap_toPosition(v_fileMap_809_, v_start_810_);
lean_dec(v_start_810_);
v_line_816_ = lean_ctor_get(v___x_815_, 0);
v_column_817_ = lean_ctor_get(v___x_815_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_861_ == 0)
{
v___x_819_ = v___x_815_;
v_isShared_820_ = v_isSharedCheck_861_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_column_817_);
lean_inc(v_line_816_);
lean_dec(v___x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_861_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v_line_822_; lean_object* v_column_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_860_; 
lean_inc_ref(v_fileMap_809_);
v___x_821_ = l_Lean_FileMap_toPosition(v_fileMap_809_, v_stop_811_);
lean_dec(v_stop_811_);
v_line_822_ = lean_ctor_get(v___x_821_, 0);
v_column_823_ = lean_ctor_get(v___x_821_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_860_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_860_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_column_823_);
lean_inc(v_line_822_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_860_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_828_ = l_Nat_reprFast(v_line_816_);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 3);
lean_ctor_set(v___x_807_, 0, v___x_828_);
v___x_830_ = v___x_807_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_859_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 5);
lean_ctor_set(v___x_825_, 1, v___x_830_);
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_830_);
v___x_832_ = v_reuseFailAlloc_858_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 5);
lean_ctor_set(v___x_819_, 1, v___x_833_);
lean_ctor_set(v___x_819_, 0, v___x_832_);
v___x_835_ = v___x_819_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_857_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = l_Nat_reprFast(v_column_817_);
v___x_837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 5);
lean_ctor_set(v___x_813_, 1, v___x_837_);
lean_ctor_set(v___x_813_, 0, v___x_835_);
v___x_839_ = v___x_813_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_856_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Nat_reprFast(v_line_822_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_827_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_833_);
v___x_848_ = l_Nat_reprFast(v_column_823_);
v___x_849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_847_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_840_);
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_843_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_801_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v_desc_708_ = v___x_855_;
v___y_709_ = v_a_517_;
v___y_710_ = v_a_518_;
goto v___jp_707_;
}
}
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_801_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v_desc_708_ = v___x_865_;
v___y_709_ = v_a_517_;
v___y_710_ = v_a_518_;
goto v___jp_707_;
}
}
v___jp_707_:
{
lean_object* v_msgLog_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_799_; 
v_msgLog_711_ = lean_ctor_get(v_diagnostics_705_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_diagnostics_705_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v_diagnostics_705_, 1);
lean_dec(v_unused_800_);
v___x_713_ = v_diagnostics_705_;
v_isShared_714_ = v_isSharedCheck_799_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_msgLog_711_);
lean_dec(v_diagnostics_705_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_799_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = l_Lean_MessageLog_toList(v_msgLog_711_);
lean_dec_ref(v_msgLog_711_);
v___x_716_ = lean_box(0);
v___x_717_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_715_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_toCold_718_; lean_object* v_options_719_; lean_object* v_a_720_; lean_object* v_ref_721_; lean_object* v_inheritedTraceOptions_722_; uint8_t v_hasTrace_723_; lean_object* v___x_724_; 
v_toCold_718_ = lean_ctor_get(v___y_709_, 0);
v_options_719_ = lean_ctor_get(v_toCold_718_, 2);
v_a_720_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_717_, 1);
v_ref_721_ = lean_ctor_get(v___y_709_, 2);
v_inheritedTraceOptions_722_ = lean_ctor_get(v_toCold_718_, 11);
v_hasTrace_723_ = lean_ctor_get_uint8(v_options_719_, sizeof(void*)*1);
v___x_724_ = lean_array_to_list(v_children_700_);
if (v_hasTrace_723_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v_a_720_);
lean_del_object(v___x_713_);
lean_dec(v_desc_708_);
lean_dec(v_infoTree_x3f_706_);
lean_del_object(v___x_702_);
v___x_725_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_724_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_734_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
return v___x_725_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_736_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_737_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_736_, v_a_720_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 5);
lean_ctor_set(v___x_713_, 1, v___x_737_);
lean_ctor_set(v___x_713_, 0, v_desc_708_);
v___x_739_ = v___x_713_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_desc_708_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_790_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___f_740_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_740_, 0, v___x_739_);
v___x_741_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_742_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_743_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_722_, v_options_719_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = l_Lean_trace_profiler;
v___x_746_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_719_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v___f_740_);
v___x_747_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_724_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_747_, 0);
lean_dec(v_unused_789_);
v___x_749_ = v___x_747_;
v_isShared_750_ = v_isSharedCheck_788_;
goto v_resetjp_748_;
}
else
{
lean_dec(v___x_747_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_788_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
if (lean_obj_tag(v_infoTree_x3f_706_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_783_; 
v_val_751_ = lean_ctor_get(v_infoTree_x3f_706_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_infoTree_x3f_706_);
if (v_isSharedCheck_783_ == 0)
{
v___x_753_ = v_infoTree_x3f_706_;
v_isShared_754_ = v_isSharedCheck_783_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_val_751_);
lean_dec(v_infoTree_x3f_706_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_783_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_756_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_722_, v_options_719_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_del_object(v___x_753_);
lean_dec(v_val_751_);
lean_del_object(v___x_702_);
v___x_758_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_758_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_del_object(v___x_749_);
v___x_762_ = lean_box(0);
v___x_763_ = l_Lean_Elab_InfoTree_format(v_val_751_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_del_object(v___x_753_);
lean_del_object(v___x_702_);
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_MessageData_ofFormat(v_a_764_);
v___x_766_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_755_, v___x_765_, v___y_709_, v___y_710_);
return v___x_766_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_782_; 
v_a_767_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_782_ == 0)
{
v___x_769_ = v___x_763_;
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_io_error_to_string(v_a_767_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 3);
lean_ctor_set(v___x_753_, 0, v___x_771_);
v___x_773_ = v___x_753_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_781_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_MessageData_ofFormat(v___x_773_);
lean_inc(v_ref_721_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_774_);
lean_ctor_set(v___x_702_, 0, v_ref_721_);
v___x_776_ = v___x_702_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_ref_721_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_776_);
v___x_778_ = v___x_769_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
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
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec(v_infoTree_x3f_706_);
lean_del_object(v___x_702_);
v___x_784_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_784_);
v___x_786_ = v___x_749_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_706_);
lean_del_object(v___x_702_);
return v___x_747_;
}
}
else
{
lean_del_object(v___x_702_);
v___y_616_ = v___x_724_;
v___y_617_ = v_inheritedTraceOptions_722_;
v___y_618_ = v_hasTrace_723_;
v___y_619_ = v___y_710_;
v___y_620_ = v_options_719_;
v___y_621_ = v___y_709_;
v___y_622_ = v___x_735_;
v___y_623_ = v_ref_721_;
v___y_624_ = v___f_740_;
v___y_625_ = v_infoTree_x3f_706_;
v___y_626_ = v___x_742_;
v___y_627_ = v___x_741_;
v___y_628_ = v___x_744_;
goto v___jp_615_;
}
}
else
{
lean_del_object(v___x_702_);
v___y_616_ = v___x_724_;
v___y_617_ = v_inheritedTraceOptions_722_;
v___y_618_ = v_hasTrace_723_;
v___y_619_ = v___y_710_;
v___y_620_ = v_options_719_;
v___y_621_ = v___y_709_;
v___y_622_ = v___x_735_;
v___y_623_ = v_ref_721_;
v___y_624_ = v___f_740_;
v___y_625_ = v_infoTree_x3f_706_;
v___y_626_ = v___x_742_;
v___y_627_ = v___x_741_;
v___y_628_ = v___x_744_;
goto v___jp_615_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_del_object(v___x_713_);
lean_dec(v_desc_708_);
lean_dec(v_infoTree_x3f_706_);
lean_del_object(v___x_702_);
lean_dec_ref(v_children_700_);
v_a_791_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_717_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_717_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
if (lean_obj_tag(v_as_867_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v_head_873_; lean_object* v_tail_874_; lean_object* v_reportingRange_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_head_873_ = lean_ctor_get(v_as_867_, 0);
lean_inc(v_head_873_);
v_tail_874_ = lean_ctor_get(v_as_867_, 1);
lean_inc(v_tail_874_);
lean_dec_ref_known(v_as_867_, 2);
v_reportingRange_875_ = lean_ctor_get(v_head_873_, 1);
lean_inc(v_reportingRange_875_);
v___x_876_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_873_);
v___x_877_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_875_, v___x_876_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_dec_ref_known(v___x_877_, 1);
v_as_867_ = v_tail_874_;
goto _start;
}
else
{
lean_dec(v_tail_874_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_884_, lean_object* v_s_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_884_, v_s_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_890_, v_x_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_896_, v_x_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_903_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_908_, lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_908_, v_x_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_box(2);
v___x_919_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_918_, v_s_914_, v_a_915_, v_a_916_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Language_SnapshotTree_trace(v_s_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_924_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Util(builtin);
}
#ifdef __cplusplus
}
#endif

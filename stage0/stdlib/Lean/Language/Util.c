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
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(lean_object* v___y_10_){
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
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_10_ = stack[0].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_10_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___boxed(lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_46_);
lean_dec(v___y_46_);
return v_res_48_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_50_);
return v___x_52_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_49_ = stack[0].m_obj;
lean_object* v___y_50_ = stack[1].m_obj;
lean_object* v_res_53_;
v_res_53_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_49_, v___y_50_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_57_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object* v_opts_58_, lean_object* v_opt_59_){
_start:
{
lean_object* v_name_60_; lean_object* v_defValue_61_; lean_object* v_map_62_; lean_object* v___x_63_; 
v_name_60_ = lean_ctor_get(v_opt_59_, 0);
v_defValue_61_ = lean_ctor_get(v_opt_59_, 1);
v_map_62_ = lean_ctor_get(v_opts_58_, 0);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_62_, v_name_60_);
if (lean_obj_tag(v___x_63_) == 0)
{
uint8_t v___x_64_; 
v___x_64_ = lean_unbox(v_defValue_61_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___x_63_, 1);
if (lean_obj_tag(v_val_65_) == 1)
{
uint8_t v_v_66_; 
v_v_66_ = lean_ctor_get_uint8(v_val_65_, 0);
lean_dec_ref_known(v_val_65_, 0);
return v_v_66_;
}
else
{
uint8_t v___x_67_; 
lean_dec(v_val_65_);
v___x_67_ = lean_unbox(v_defValue_61_);
return v___x_67_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_58_ = stack[0].m_obj;
lean_object* v_opt_59_ = stack[1].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_58_, v_opt_59_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object* v_opts_69_, lean_object* v_opt_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_69_, v_opt_70_);
lean_dec_ref(v_opt_70_);
lean_dec_ref(v_opts_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object* v___x_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_73_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_73_ = stack[0].m_obj;
lean_object* v_x_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v___y_76_ = stack[3].m_obj;
lean_object* v_res_80_;
v_res_80_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(v___x_73_, v_x_74_, v___y_75_, v___y_76_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object* v___x_81_, lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(v___x_81_, v_x_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec_ref(v_x_82_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_87_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_91_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
lean_ctor_set(v___x_93_, 3, v___x_92_);
lean_ctor_set(v___x_93_, 4, v___x_91_);
lean_ctor_set(v___x_93_, 5, v___x_91_);
lean_ctor_set(v___x_93_, 6, v___x_91_);
lean_ctor_set(v___x_93_, 7, v___x_91_);
lean_ctor_set(v___x_93_, 8, v___x_91_);
lean_ctor_set(v___x_93_, 9, v___x_91_);
lean_ctor_set(v___x_93_, 10, v___x_91_);
lean_ctor_set(v___x_93_, 11, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_97_ = ((size_t)5ULL);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_unsigned_to_nat(32u);
v___x_100_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
v___x_102_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_98_);
lean_ctor_set(v___x_102_, 3, v___x_98_);
lean_ctor_set_usize(v___x_102_, 4, v___x_97_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_box(1);
v___x_104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
v___x_105_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object* v_msgData_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_toCold_112_; lean_object* v_env_113_; lean_object* v_options_114_; uint8_t v___x_115_; lean_object* v_env_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_111_ = lean_st_ref_get(v___y_109_);
v_toCold_112_ = lean_ctor_get(v___y_108_, 0);
v_env_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_env_113_);
lean_dec(v___x_111_);
v_options_114_ = lean_ctor_get(v_toCold_112_, 2);
v___x_115_ = 0;
v_env_116_ = l_Lean_Environment_setRecordingDeps(v_env_113_, v___x_115_);
v___x_117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_114_);
v___x_119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_119_, 0, v_env_116_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
lean_ctor_set(v___x_119_, 3, v_options_114_);
v___x_120_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_msgData_107_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_107_ = stack[0].m_obj;
lean_object* v___y_108_ = stack[1].m_obj;
lean_object* v___y_109_ = stack[2].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_107_, v___y_108_, v___y_109_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_127_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_128_; double v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_float_of_nat(v___x_128_);
return v___x_129_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_133_, lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_ref_138_; lean_object* v___x_139_; lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_185_; 
v_ref_138_ = lean_ctor_get(v___y_135_, 2);
v___x_139_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_134_, v___y_135_, v___y_136_);
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_185_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_185_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_185_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v_traceState_145_; lean_object* v_env_146_; lean_object* v_nextMacroScope_147_; lean_object* v_ngen_148_; lean_object* v_auxDeclNGen_149_; lean_object* v_cache_150_; lean_object* v_recordedDeps_151_; lean_object* v_messages_152_; lean_object* v_infoState_153_; lean_object* v_snapshotTasks_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_184_; 
v___x_144_ = lean_st_ref_take(v___y_136_);
v_traceState_145_ = lean_ctor_get(v___x_144_, 4);
v_env_146_ = lean_ctor_get(v___x_144_, 0);
v_nextMacroScope_147_ = lean_ctor_get(v___x_144_, 1);
v_ngen_148_ = lean_ctor_get(v___x_144_, 2);
v_auxDeclNGen_149_ = lean_ctor_get(v___x_144_, 3);
v_cache_150_ = lean_ctor_get(v___x_144_, 5);
v_recordedDeps_151_ = lean_ctor_get(v___x_144_, 6);
v_messages_152_ = lean_ctor_get(v___x_144_, 7);
v_infoState_153_ = lean_ctor_get(v___x_144_, 8);
v_snapshotTasks_154_ = lean_ctor_get(v___x_144_, 9);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_184_ == 0)
{
v___x_156_ = v___x_144_;
v_isShared_157_ = v_isSharedCheck_184_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snapshotTasks_154_);
lean_inc(v_infoState_153_);
lean_inc(v_messages_152_);
lean_inc(v_recordedDeps_151_);
lean_inc(v_cache_150_);
lean_inc(v_traceState_145_);
lean_inc(v_auxDeclNGen_149_);
lean_inc(v_ngen_148_);
lean_inc(v_nextMacroScope_147_);
lean_inc(v_env_146_);
lean_dec(v___x_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_184_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint64_t v_tid_158_; lean_object* v_traces_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_183_; 
v_tid_158_ = lean_ctor_get_uint64(v_traceState_145_, sizeof(void*)*1);
v_traces_159_ = lean_ctor_get(v_traceState_145_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_traceState_145_);
if (v_isSharedCheck_183_ == 0)
{
v___x_161_ = v_traceState_145_;
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_traces_159_);
lean_dec(v_traceState_145_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; double v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_box(0);
v___x_165_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_166_ = 0;
v___x_167_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_168_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_168_, 0, v_cls_133_);
lean_ctor_set(v___x_168_, 1, v___x_164_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set_float(v___x_168_, sizeof(void*)*3, v___x_165_);
lean_ctor_set_float(v___x_168_, sizeof(void*)*3 + 8, v___x_165_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*3 + 16, v___x_166_);
v___x_169_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_170_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v_a_140_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_inc(v_ref_138_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_138_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lean_PersistentArray_push___redArg(v_traces_159_, v___x_171_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_172_);
v___x_174_ = v___x_161_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_172_);
lean_ctor_set_uint64(v_reuseFailAlloc_182_, sizeof(void*)*1, v_tid_158_);
v___x_174_ = v_reuseFailAlloc_182_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 4, v___x_174_);
v___x_176_ = v___x_156_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_env_146_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_nextMacroScope_147_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_ngen_148_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_auxDeclNGen_149_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_181_, 5, v_cache_150_);
lean_ctor_set(v_reuseFailAlloc_181_, 6, v_recordedDeps_151_);
lean_ctor_set(v_reuseFailAlloc_181_, 7, v_messages_152_);
lean_ctor_set(v_reuseFailAlloc_181_, 8, v_infoState_153_);
lean_ctor_set(v_reuseFailAlloc_181_, 9, v_snapshotTasks_154_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_st_ref_put(v___y_136_, v___x_176_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_163_);
v___x_179_ = v___x_142_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_163_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_133_ = stack[0].m_obj;
lean_object* v_msg_134_ = stack[1].m_obj;
lean_object* v___y_135_ = stack[2].m_obj;
lean_object* v___y_136_ = stack[3].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_133_, v_msg_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_187_, lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_187_, v_msg_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_dec(v_pre_193_);
return v_x_194_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_207_; 
v_head_196_ = lean_ctor_get(v_x_195_, 0);
v_tail_197_ = lean_ctor_get(v_x_195_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_207_ == 0)
{
v___x_199_ = v_x_195_;
v_isShared_200_ = v_isSharedCheck_207_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_tail_197_);
lean_inc(v_head_196_);
lean_dec(v_x_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_207_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
lean_inc(v_pre_193_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 5);
lean_ctor_set(v___x_199_, 1, v_pre_193_);
lean_ctor_set(v___x_199_, 0, v_x_194_);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_x_194_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_pre_193_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_203_, 0, v_head_196_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v_x_194_ = v___x_204_;
v_x_195_ = v_tail_197_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v___x_210_; 
lean_dec(v_pre_208_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_head_211_; lean_object* v_tail_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
v_head_211_ = lean_ctor_get(v_x_209_, 0);
v_tail_212_ = lean_ctor_get(v_x_209_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_221_ == 0)
{
v___x_214_ = v_x_209_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_tail_212_);
lean_inc(v_head_211_);
lean_dec(v_x_209_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_216_, 0, v_head_211_);
lean_inc(v_pre_208_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 5);
lean_ctor_set(v___x_214_, 1, v___x_216_);
lean_ctor_set(v___x_214_, 0, v_pre_208_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_pre_208_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; 
v___x_219_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_208_, v___x_218_, v_tail_212_);
return v___x_219_;
}
}
}
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_List_reverse___redArg(v_x_223_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_head_227_; lean_object* v_tail_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_238_; 
v_head_227_ = lean_ctor_get(v_x_222_, 0);
v_tail_228_ = lean_ctor_get(v_x_222_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_238_ == 0)
{
v___x_230_ = v_x_222_;
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_tail_228_);
lean_inc(v_head_227_);
lean_dec(v_x_222_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = 0;
v___x_233_ = l_Lean_Message_toString(v_head_227_, v___x_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_x_223_);
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_x_223_);
v___x_235_ = v_reuseFailAlloc_237_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v_x_222_ = v_tail_228_;
v_x_223_ = v___x_235_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_222_ = stack[0].m_obj;
lean_object* v_x_223_ = stack[1].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_222_, v_x_223_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_240_, v_x_241_);
return v_res_243_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v_x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v_x_244_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v_x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v_x_244_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v_x_244_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v_x_244_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 0);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_244_ = stack[0].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_244_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
lean_object* v_name_268_; lean_object* v_defValue_269_; lean_object* v_map_270_; lean_object* v___x_271_; 
v_name_268_ = lean_ctor_get(v_opt_267_, 0);
v_defValue_269_ = lean_ctor_get(v_opt_267_, 1);
v_map_270_ = lean_ctor_get(v_opts_266_, 0);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_270_, v_name_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_inc(v_defValue_269_);
return v_defValue_269_;
}
else
{
lean_object* v_val_272_; 
v_val_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v___x_271_, 1);
if (lean_obj_tag(v_val_272_) == 3)
{
lean_object* v_v_273_; 
v_v_273_ = lean_ctor_get(v_val_272_, 0);
lean_inc(v_v_273_);
lean_dec_ref_known(v_val_272_, 1);
return v_v_273_;
}
else
{
lean_dec(v_val_272_);
lean_inc(v_defValue_269_);
return v_defValue_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_274_, lean_object* v_opt_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_274_, v_opt_275_);
lean_dec_ref(v_opt_275_);
lean_dec_ref(v_opts_274_);
return v_res_276_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_277_, size_t v_i_278_, lean_object* v_bs_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_lt(v_i_278_, v_sz_277_);
if (v___x_280_ == 0)
{
return v_bs_279_;
}
else
{
lean_object* v_v_281_; lean_object* v_msg_282_; lean_object* v___x_283_; lean_object* v_bs_x27_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_v_281_ = lean_array_uget_borrowed(v_bs_279_, v_i_278_);
v_msg_282_ = lean_ctor_get(v_v_281_, 1);
lean_inc_ref(v_msg_282_);
v___x_283_ = lean_unsigned_to_nat(0u);
v_bs_x27_284_ = lean_array_uset(v_bs_279_, v_i_278_, v___x_283_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_278_, v___x_285_);
v___x_287_ = lean_array_uset(v_bs_x27_284_, v_i_278_, v_msg_282_);
v_i_278_ = v___x_286_;
v_bs_279_ = v___x_287_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_277_ = stack[0].m_num;
size_t v_i_278_ = stack[1].m_num;
lean_object* v_bs_279_ = stack[2].m_obj;
lean_object* v_res_289_;
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_277_, v_i_278_, v_bs_279_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_290_, lean_object* v_i_291_, lean_object* v_bs_292_){
_start:
{
size_t v_sz_boxed_293_; size_t v_i_boxed_294_; lean_object* v_res_295_; 
v_sz_boxed_293_ = lean_unbox_usize(v_sz_290_);
lean_dec(v_sz_290_);
v_i_boxed_294_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_293_, v_i_boxed_294_, v_bs_292_);
return v_res_295_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_296_, lean_object* v_data_297_, lean_object* v_ref_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_toCold_303_; lean_object* v_currRecDepth_304_; lean_object* v_ref_305_; uint16_t v_optionFlags_306_; uint8_t v_suppressElabErrors_307_; uint8_t v_isRecordingDeps_308_; lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_traceState_312_; lean_object* v_traces_313_; lean_object* v___x_314_; size_t v_sz_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v_msg_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_358_; 
v_toCold_303_ = lean_ctor_get(v___y_300_, 0);
v_currRecDepth_304_ = lean_ctor_get(v___y_300_, 1);
v_ref_305_ = lean_ctor_get(v___y_300_, 2);
v_optionFlags_306_ = lean_ctor_get_uint16(v___y_300_, sizeof(void*)*3);
v_suppressElabErrors_307_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*3 + 2);
v_isRecordingDeps_308_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*3 + 3);
v_ref_309_ = l_Lean_replaceRef(v_ref_298_, v_ref_305_);
lean_inc(v_currRecDepth_304_);
lean_inc_ref(v_toCold_303_);
v___x_310_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_310_, 0, v_toCold_303_);
lean_ctor_set(v___x_310_, 1, v_currRecDepth_304_);
lean_ctor_set(v___x_310_, 2, v_ref_309_);
lean_ctor_set_uint16(v___x_310_, sizeof(void*)*3, v_optionFlags_306_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*3 + 2, v_suppressElabErrors_307_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*3 + 3, v_isRecordingDeps_308_);
v___x_311_ = lean_st_ref_get(v___y_301_);
v_traceState_312_ = lean_ctor_get(v___x_311_, 4);
lean_inc_ref(v_traceState_312_);
lean_dec(v___x_311_);
v_traces_313_ = lean_ctor_get(v_traceState_312_, 0);
lean_inc_ref(v_traces_313_);
lean_dec_ref(v_traceState_312_);
v___x_314_ = l_Lean_PersistentArray_toArray___redArg(v_traces_313_);
lean_dec_ref(v_traces_313_);
v_sz_315_ = lean_array_size(v___x_314_);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_315_, v___x_316_, v___x_314_);
v_msg_318_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_318_, 0, v_data_297_);
lean_ctor_set(v_msg_318_, 1, v_msg_299_);
lean_ctor_set(v_msg_318_, 2, v___x_317_);
v___x_319_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_318_, v___x_310_, v___y_301_);
lean_dec_ref_known(v___x_310_, 3);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_358_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_358_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_358_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v_traceState_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_cache_330_; lean_object* v_recordedDeps_331_; lean_object* v_messages_332_; lean_object* v_infoState_333_; lean_object* v_snapshotTasks_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_357_; 
v___x_324_ = lean_st_ref_take(v___y_301_);
v_traceState_325_ = lean_ctor_get(v___x_324_, 4);
v_env_326_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_324_, 1);
v_ngen_328_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_324_, 3);
v_cache_330_ = lean_ctor_get(v___x_324_, 5);
v_recordedDeps_331_ = lean_ctor_get(v___x_324_, 6);
v_messages_332_ = lean_ctor_get(v___x_324_, 7);
v_infoState_333_ = lean_ctor_get(v___x_324_, 8);
v_snapshotTasks_334_ = lean_ctor_get(v___x_324_, 9);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_357_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_357_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snapshotTasks_334_);
lean_inc(v_infoState_333_);
lean_inc(v_messages_332_);
lean_inc(v_recordedDeps_331_);
lean_inc(v_cache_330_);
lean_inc(v_traceState_325_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_357_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v_tid_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_355_; 
v_tid_338_ = lean_ctor_get_uint64(v_traceState_325_, sizeof(void*)*1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_traceState_325_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v_traceState_325_, 0);
lean_dec(v_unused_356_);
v___x_340_ = v_traceState_325_;
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_traceState_325_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_ref_298_);
lean_ctor_set(v___x_343_, 1, v_a_320_);
v___x_344_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_296_, v___x_343_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_344_);
lean_ctor_set_uint64(v_reuseFailAlloc_354_, sizeof(void*)*1, v_tid_338_);
v___x_346_ = v_reuseFailAlloc_354_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_346_);
v___x_348_ = v___x_336_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_env_326_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_353_, 5, v_cache_330_);
lean_ctor_set(v_reuseFailAlloc_353_, 6, v_recordedDeps_331_);
lean_ctor_set(v_reuseFailAlloc_353_, 7, v_messages_332_);
lean_ctor_set(v_reuseFailAlloc_353_, 8, v_infoState_333_);
lean_ctor_set(v_reuseFailAlloc_353_, 9, v_snapshotTasks_334_);
v___x_348_ = v_reuseFailAlloc_353_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_st_ref_put(v___y_301_, v___x_348_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_342_);
v___x_351_ = v___x_322_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_342_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_296_ = stack[0].m_obj;
lean_object* v_data_297_ = stack[1].m_obj;
lean_object* v_ref_298_ = stack[2].m_obj;
lean_object* v_msg_299_ = stack[3].m_obj;
lean_object* v___y_300_ = stack[4].m_obj;
lean_object* v___y_301_ = stack[5].m_obj;
lean_object* v_res_359_;
v_res_359_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_296_, v_data_297_, v_ref_298_, v_msg_299_, v___y_300_, v___y_301_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_360_, lean_object* v_data_361_, lean_object* v_ref_362_, lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_360_, v_data_361_, v_ref_362_, v_msg_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_367_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_368_){
_start:
{
if (lean_obj_tag(v_e_368_) == 0)
{
uint8_t v___x_369_; 
v___x_369_ = 2;
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_368_ = stack[0].m_obj;
uint8_t v_res_371_;
v_res_371_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_368_);
stack->m_num = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_372_);
lean_dec_ref(v_e_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_378_; double v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(1000u);
v___x_379_ = lean_float_of_nat(v___x_378_);
return v___x_379_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_380_, uint8_t v_collapsed_381_, lean_object* v_tag_382_, lean_object* v_opts_383_, uint8_t v_clsEnabled_384_, lean_object* v_oldTraces_385_, lean_object* v_msg_386_, lean_object* v_resStartStop_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v_data_396_; lean_object* v_fst_399_; lean_object* v_snd_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___y_404_; lean_object* v_a_405_; uint8_t v___y_420_; double v___y_452_; 
v_fst_391_ = lean_ctor_get(v_resStartStop_387_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_resStartStop_387_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v_resStartStop_387_);
v_fst_399_ = lean_ctor_get(v_snd_392_, 0);
lean_inc(v_fst_399_);
v_snd_400_ = lean_ctor_get(v_snd_392_, 1);
lean_inc(v_snd_400_);
lean_dec(v_snd_392_);
v___x_401_ = l_Lean_trace_profiler;
v___x_402_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_383_, v___x_401_);
if (v___x_402_ == 0)
{
v___y_420_ = v___x_402_;
goto v___jp_419_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = l_Lean_trace_profiler_useHeartbeats;
v___x_458_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_383_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; double v___x_461_; double v___x_462_; double v___x_463_; 
v___x_459_ = l_Lean_trace_profiler_threshold;
v___x_460_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_383_, v___x_459_);
v___x_461_ = lean_float_of_nat(v___x_460_);
v___x_462_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_463_ = lean_float_div(v___x_461_, v___x_462_);
v___y_452_ = v___x_463_;
goto v___jp_451_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; double v___x_466_; 
v___x_464_ = l_Lean_trace_profiler_threshold;
v___x_465_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_383_, v___x_464_);
v___x_466_ = lean_float_of_nat(v___x_465_);
v___y_452_ = v___x_466_;
goto v___jp_451_;
}
}
v___jp_393_:
{
lean_object* v___x_397_; 
lean_inc(v___y_394_);
v___x_397_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_385_, v_data_396_, v___y_394_, v___y_395_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
lean_dec_ref_known(v___x_397_, 1);
v___x_398_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_391_);
return v___x_398_;
}
else
{
lean_dec(v_fst_391_);
return v___x_397_;
}
}
v___jp_403_:
{
uint8_t v_result_406_; lean_object* v___x_407_; lean_object* v___x_408_; double v___x_409_; lean_object* v_data_410_; 
v_result_406_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_391_);
v___x_407_ = lean_box(v_result_406_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_382_);
lean_inc_ref(v___x_408_);
lean_inc(v_cls_380_);
v_data_410_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_410_, 0, v_cls_380_);
lean_ctor_set(v_data_410_, 1, v___x_408_);
lean_ctor_set(v_data_410_, 2, v_tag_382_);
lean_ctor_set_float(v_data_410_, sizeof(void*)*3, v___x_409_);
lean_ctor_set_float(v_data_410_, sizeof(void*)*3 + 8, v___x_409_);
lean_ctor_set_uint8(v_data_410_, sizeof(void*)*3 + 16, v_collapsed_381_);
if (v___x_402_ == 0)
{
lean_dec_ref_known(v___x_408_, 1);
lean_dec(v_snd_400_);
lean_dec(v_fst_399_);
lean_dec_ref(v_tag_382_);
lean_dec(v_cls_380_);
v___y_394_ = v___y_404_;
v___y_395_ = v_a_405_;
v_data_396_ = v_data_410_;
goto v___jp_393_;
}
else
{
lean_object* v_data_411_; double v___x_412_; double v___x_413_; 
lean_dec_ref_known(v_data_410_, 3);
v_data_411_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_411_, 0, v_cls_380_);
lean_ctor_set(v_data_411_, 1, v___x_408_);
lean_ctor_set(v_data_411_, 2, v_tag_382_);
v___x_412_ = lean_unbox_float(v_fst_399_);
lean_dec(v_fst_399_);
lean_ctor_set_float(v_data_411_, sizeof(void*)*3, v___x_412_);
v___x_413_ = lean_unbox_float(v_snd_400_);
lean_dec(v_snd_400_);
lean_ctor_set_float(v_data_411_, sizeof(void*)*3 + 8, v___x_413_);
lean_ctor_set_uint8(v_data_411_, sizeof(void*)*3 + 16, v_collapsed_381_);
v___y_394_ = v___y_404_;
v___y_395_ = v_a_405_;
v_data_396_ = v_data_411_;
goto v___jp_393_;
}
}
v___jp_414_:
{
lean_object* v_ref_415_; lean_object* v___x_416_; 
v_ref_415_ = lean_ctor_get(v___y_388_, 2);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v_fst_391_);
v___x_416_ = lean_apply_4(v_msg_386_, v_fst_391_, v___y_388_, v___y_389_, lean_box(0));
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___y_404_ = v_ref_415_;
v_a_405_ = v_a_417_;
goto v___jp_403_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_404_ = v_ref_415_;
v_a_405_ = v___x_418_;
goto v___jp_403_;
}
}
v___jp_419_:
{
if (v_clsEnabled_384_ == 0)
{
if (v___y_420_ == 0)
{
lean_object* v___x_421_; lean_object* v_traceState_422_; lean_object* v_env_423_; lean_object* v_nextMacroScope_424_; lean_object* v_ngen_425_; lean_object* v_auxDeclNGen_426_; lean_object* v_cache_427_; lean_object* v_recordedDeps_428_; lean_object* v_messages_429_; lean_object* v_infoState_430_; lean_object* v_snapshotTasks_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_snd_400_);
lean_dec(v_fst_399_);
lean_dec_ref(v_msg_386_);
lean_dec_ref(v_tag_382_);
lean_dec(v_cls_380_);
v___x_421_ = lean_st_ref_take(v___y_389_);
v_traceState_422_ = lean_ctor_get(v___x_421_, 4);
v_env_423_ = lean_ctor_get(v___x_421_, 0);
v_nextMacroScope_424_ = lean_ctor_get(v___x_421_, 1);
v_ngen_425_ = lean_ctor_get(v___x_421_, 2);
v_auxDeclNGen_426_ = lean_ctor_get(v___x_421_, 3);
v_cache_427_ = lean_ctor_get(v___x_421_, 5);
v_recordedDeps_428_ = lean_ctor_get(v___x_421_, 6);
v_messages_429_ = lean_ctor_get(v___x_421_, 7);
v_infoState_430_ = lean_ctor_get(v___x_421_, 8);
v_snapshotTasks_431_ = lean_ctor_get(v___x_421_, 9);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_450_ == 0)
{
v___x_433_ = v___x_421_;
v_isShared_434_ = v_isSharedCheck_450_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snapshotTasks_431_);
lean_inc(v_infoState_430_);
lean_inc(v_messages_429_);
lean_inc(v_recordedDeps_428_);
lean_inc(v_cache_427_);
lean_inc(v_traceState_422_);
lean_inc(v_auxDeclNGen_426_);
lean_inc(v_ngen_425_);
lean_inc(v_nextMacroScope_424_);
lean_inc(v_env_423_);
lean_dec(v___x_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_450_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint64_t v_tid_435_; lean_object* v_traces_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_449_; 
v_tid_435_ = lean_ctor_get_uint64(v_traceState_422_, sizeof(void*)*1);
v_traces_436_ = lean_ctor_get(v_traceState_422_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_traceState_422_);
if (v_isSharedCheck_449_ == 0)
{
v___x_438_ = v_traceState_422_;
v_isShared_439_ = v_isSharedCheck_449_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_traces_436_);
lean_dec(v_traceState_422_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_449_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_385_, v_traces_436_);
lean_dec_ref(v_traces_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_440_);
lean_ctor_set_uint64(v_reuseFailAlloc_448_, sizeof(void*)*1, v_tid_435_);
v___x_442_ = v_reuseFailAlloc_448_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v___x_442_);
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_env_423_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_nextMacroScope_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_ngen_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_auxDeclNGen_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v_cache_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_recordedDeps_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_messages_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 9, v_snapshotTasks_431_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_st_ref_put(v___y_389_, v___x_444_);
v___x_446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_391_);
return v___x_446_;
}
}
}
}
}
else
{
goto v___jp_414_;
}
}
else
{
goto v___jp_414_;
}
}
v___jp_451_:
{
double v___x_453_; double v___x_454_; double v___x_455_; uint8_t v___x_456_; 
v___x_453_ = lean_unbox_float(v_snd_400_);
v___x_454_ = lean_unbox_float(v_fst_399_);
v___x_455_ = lean_float_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_float_decLt(v___y_452_, v___x_455_);
v___y_420_ = v___x_456_;
goto v___jp_419_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_380_ = stack[0].m_obj;
uint8_t v_collapsed_381_ = stack[1].m_num;
lean_object* v_tag_382_ = stack[2].m_obj;
lean_object* v_opts_383_ = stack[3].m_obj;
uint8_t v_clsEnabled_384_ = stack[4].m_num;
lean_object* v_oldTraces_385_ = stack[5].m_obj;
lean_object* v_msg_386_ = stack[6].m_obj;
lean_object* v_resStartStop_387_ = stack[7].m_obj;
lean_object* v___y_388_ = stack[8].m_obj;
lean_object* v___y_389_ = stack[9].m_obj;
lean_object* v_res_467_;
v_res_467_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_380_, v_collapsed_381_, v_tag_382_, v_opts_383_, v_clsEnabled_384_, v_oldTraces_385_, v_msg_386_, v_resStartStop_387_, v___y_388_, v___y_389_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_468_, lean_object* v_collapsed_469_, lean_object* v_tag_470_, lean_object* v_opts_471_, lean_object* v_clsEnabled_472_, lean_object* v_oldTraces_473_, lean_object* v_msg_474_, lean_object* v_resStartStop_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v_collapsed_boxed_479_; uint8_t v_clsEnabled_boxed_480_; lean_object* v_res_481_; 
v_collapsed_boxed_479_ = lean_unbox(v_collapsed_469_);
v_clsEnabled_boxed_480_ = lean_unbox(v_clsEnabled_472_);
v_res_481_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_468_, v_collapsed_boxed_479_, v_tag_470_, v_opts_471_, v_clsEnabled_boxed_480_, v_oldTraces_473_, v_msg_474_, v_resStartStop_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_opts_471_);
return v_res_481_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_482_; double v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1000000000u);
v___x_483_ = lean_float_of_nat(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_497_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_498_ = l_Lean_Name_append(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_503_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_504_ = l_Lean_Name_append(v___x_503_, v___x_502_);
return v___x_504_;
}
}
lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_526_, lean_object* v_s_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_a_542_; uint8_t v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v_a_562_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v_a_575_; lean_object* v___y_578_; uint8_t v___y_579_; lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_592_; uint8_t v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v_a_602_; lean_object* v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; uint8_t v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_a_625_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v_a_638_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v_element_732_; lean_object* v_children_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_899_; 
v_element_732_ = lean_ctor_get(v_s_527_, 0);
v_children_733_ = lean_ctor_get(v_s_527_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_s_527_);
if (v_isSharedCheck_899_ == 0)
{
v___x_735_ = v_s_527_;
v_isShared_736_ = v_isSharedCheck_899_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_children_733_);
lean_inc(v_element_732_);
lean_dec(v_s_527_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_899_;
goto v_resetjp_734_;
}
v___jp_531_:
{
lean_object* v___x_543_; double v___x_544_; double v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = lean_float_of_nat(v___y_538_);
v___x_545_ = lean_float_of_nat(v___x_543_);
v___x_546_ = lean_box_float(v___x_544_);
v___x_547_ = lean_box_float(v___x_545_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_542_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_537_);
v___x_550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_537_, v___y_533_, v___y_536_, v___y_532_, v___y_535_, v___y_539_, v___y_534_, v___x_549_, v___y_541_, v___y_540_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v_a_562_);
v___y_532_ = v___y_553_;
v___y_533_ = v___y_552_;
v___y_534_ = v___y_554_;
v___y_535_ = v___y_557_;
v___y_536_ = v___y_556_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_558_;
v___y_539_ = v___y_559_;
v___y_540_ = v___y_561_;
v___y_541_ = v___y_560_;
v_a_542_ = v___x_563_;
goto v___jp_531_;
}
v___jp_564_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_a_575_);
v___y_532_ = v___y_566_;
v___y_533_ = v___y_565_;
v___y_534_ = v___y_567_;
v___y_535_ = v___y_570_;
v___y_536_ = v___y_569_;
v___y_537_ = v___y_568_;
v___y_538_ = v___y_571_;
v___y_539_ = v___y_572_;
v___y_540_ = v___y_574_;
v___y_541_ = v___y_573_;
v_a_542_ = v___x_576_;
goto v___jp_531_;
}
v___jp_577_:
{
if (lean_obj_tag(v___y_588_) == 0)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___y_588_, 1);
v___y_552_ = v___y_579_;
v___y_553_ = v___y_578_;
v___y_554_ = v___y_580_;
v___y_555_ = v___y_583_;
v___y_556_ = v___y_582_;
v___y_557_ = v___y_581_;
v___y_558_ = v___y_584_;
v___y_559_ = v___y_585_;
v___y_560_ = v___y_587_;
v___y_561_ = v___y_586_;
v_a_562_ = v_a_589_;
goto v___jp_551_;
}
else
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___y_588_, 1);
v___y_565_ = v___y_579_;
v___y_566_ = v___y_578_;
v___y_567_ = v___y_580_;
v___y_568_ = v___y_583_;
v___y_569_ = v___y_582_;
v___y_570_ = v___y_581_;
v___y_571_ = v___y_584_;
v___y_572_ = v___y_585_;
v___y_573_ = v___y_587_;
v___y_574_ = v___y_586_;
v_a_575_ = v_a_590_;
goto v___jp_564_;
}
}
v___jp_591_:
{
lean_object* v___x_603_; double v___x_604_; double v___x_605_; double v___x_606_; double v___x_607_; double v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_603_ = lean_io_mono_nanos_now();
v___x_604_ = lean_float_of_nat(v___y_594_);
v___x_605_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_606_ = lean_float_div(v___x_604_, v___x_605_);
v___x_607_ = lean_float_of_nat(v___x_603_);
v___x_608_ = lean_float_div(v___x_607_, v___x_605_);
v___x_609_ = lean_box_float(v___x_606_);
v___x_610_ = lean_box_float(v___x_608_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_602_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_inc_ref(v___y_597_);
lean_inc(v___y_598_);
v___x_613_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_598_, v___y_593_, v___y_597_, v___y_592_, v___y_596_, v___y_599_, v___y_595_, v___x_612_, v___y_601_, v___y_600_);
return v___x_613_;
}
v___jp_614_:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_a_625_);
v___y_592_ = v___y_617_;
v___y_593_ = v___y_616_;
v___y_594_ = v___y_615_;
v___y_595_ = v___y_618_;
v___y_596_ = v___y_621_;
v___y_597_ = v___y_620_;
v___y_598_ = v___y_619_;
v___y_599_ = v___y_622_;
v___y_600_ = v___y_624_;
v___y_601_ = v___y_623_;
v_a_602_ = v___x_626_;
goto v___jp_591_;
}
v___jp_627_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_a_638_);
v___y_592_ = v___y_630_;
v___y_593_ = v___y_629_;
v___y_594_ = v___y_628_;
v___y_595_ = v___y_631_;
v___y_596_ = v___y_634_;
v___y_597_ = v___y_633_;
v___y_598_ = v___y_632_;
v___y_599_ = v___y_635_;
v___y_600_ = v___y_637_;
v___y_601_ = v___y_636_;
v_a_602_ = v___x_639_;
goto v___jp_591_;
}
v___jp_640_:
{
if (lean_obj_tag(v___y_651_) == 0)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v___y_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___y_651_, 1);
v___y_615_ = v___y_643_;
v___y_616_ = v___y_642_;
v___y_617_ = v___y_641_;
v___y_618_ = v___y_644_;
v___y_619_ = v___y_647_;
v___y_620_ = v___y_646_;
v___y_621_ = v___y_645_;
v___y_622_ = v___y_648_;
v___y_623_ = v___y_650_;
v___y_624_ = v___y_649_;
v_a_625_ = v_a_652_;
goto v___jp_614_;
}
else
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v___y_651_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___y_651_, 1);
v___y_628_ = v___y_643_;
v___y_629_ = v___y_642_;
v___y_630_ = v___y_641_;
v___y_631_ = v___y_644_;
v___y_632_ = v___y_647_;
v___y_633_ = v___y_646_;
v___y_634_ = v___y_645_;
v___y_635_ = v___y_648_;
v___y_636_ = v___y_650_;
v___y_637_ = v___y_649_;
v_a_638_ = v_a_653_;
goto v___jp_627_;
}
}
v___jp_654_:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_trace_profiler_useHeartbeats;
v___x_671_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_659_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_io_mono_nanos_now();
v___x_673_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_661_, v___y_658_, v___y_667_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_dec_ref_known(v___x_673_, 1);
if (lean_obj_tag(v___y_662_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_val_674_ = lean_ctor_get(v___y_662_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v___y_662_, 1);
v___x_675_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_656_);
v___x_676_ = l_Lean_Name_mkStr2(v___y_656_, v___x_675_);
v___x_677_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_676_);
v___x_678_ = l_Lean_Name_append(v___x_677_, v___x_676_);
v___x_679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_666_, v___y_659_, v___x_678_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v___x_676_);
lean_dec(v_val_674_);
v___x_680_ = lean_box(0);
v___y_615_ = v___x_672_;
v___y_616_ = v___y_655_;
v___y_617_ = v___y_659_;
v___y_618_ = v___y_660_;
v___y_619_ = v___y_664_;
v___y_620_ = v___y_663_;
v___y_621_ = v___y_657_;
v___y_622_ = v_a_669_;
v___y_623_ = v___y_658_;
v___y_624_ = v___y_667_;
v_a_625_ = v___x_680_;
goto v___jp_614_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Lean_Elab_InfoTree_format(v_val_674_, v___x_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = l_Lean_MessageData_ofFormat(v_a_683_);
v___x_685_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_676_, v___x_684_, v___y_658_, v___y_667_);
v___y_641_ = v___y_659_;
v___y_642_ = v___y_655_;
v___y_643_ = v___x_672_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_657_;
v___y_646_ = v___y_663_;
v___y_647_ = v___y_664_;
v___y_648_ = v_a_669_;
v___y_649_ = v___y_667_;
v___y_650_ = v___y_658_;
v___y_651_ = v___x_685_;
goto v___jp_640_;
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___x_676_);
v_a_686_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v___x_682_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_682_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_io_error_to_string(v_a_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 3);
lean_ctor_set(v___x_688_, 0, v___x_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_MessageData_ofFormat(v___x_692_);
lean_inc(v___y_665_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___y_665_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___y_628_ = v___x_672_;
v___y_629_ = v___y_655_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_660_;
v___y_632_ = v___y_664_;
v___y_633_ = v___y_663_;
v___y_634_ = v___y_657_;
v___y_635_ = v_a_669_;
v___y_636_ = v___y_658_;
v___y_637_ = v___y_667_;
v_a_638_ = v___x_694_;
goto v___jp_627_;
}
}
}
}
}
else
{
lean_object* v___x_697_; 
lean_dec(v___y_662_);
v___x_697_ = lean_box(0);
v___y_615_ = v___x_672_;
v___y_616_ = v___y_655_;
v___y_617_ = v___y_659_;
v___y_618_ = v___y_660_;
v___y_619_ = v___y_664_;
v___y_620_ = v___y_663_;
v___y_621_ = v___y_657_;
v___y_622_ = v_a_669_;
v___y_623_ = v___y_658_;
v___y_624_ = v___y_667_;
v_a_625_ = v___x_697_;
goto v___jp_614_;
}
}
else
{
lean_dec(v___y_662_);
v___y_641_ = v___y_659_;
v___y_642_ = v___y_655_;
v___y_643_ = v___x_672_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_657_;
v___y_646_ = v___y_663_;
v___y_647_ = v___y_664_;
v___y_648_ = v_a_669_;
v___y_649_ = v___y_667_;
v___y_650_ = v___y_658_;
v___y_651_ = v___x_673_;
goto v___jp_640_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_io_get_num_heartbeats();
v___x_699_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_661_, v___y_658_, v___y_667_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_dec_ref_known(v___x_699_, 1);
if (lean_obj_tag(v___y_662_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_val_700_ = lean_ctor_get(v___y_662_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___y_662_, 1);
v___x_701_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_656_);
v___x_702_ = l_Lean_Name_mkStr2(v___y_656_, v___x_701_);
v___x_703_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_702_);
v___x_704_ = l_Lean_Name_append(v___x_703_, v___x_702_);
v___x_705_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_666_, v___y_659_, v___x_704_);
lean_dec(v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v___x_702_);
lean_dec(v_val_700_);
v___x_706_ = lean_box(0);
v___y_552_ = v___y_655_;
v___y_553_ = v___y_659_;
v___y_554_ = v___y_660_;
v___y_555_ = v___y_664_;
v___y_556_ = v___y_663_;
v___y_557_ = v___y_657_;
v___y_558_ = v___x_698_;
v___y_559_ = v_a_669_;
v___y_560_ = v___y_658_;
v___y_561_ = v___y_667_;
v_a_562_ = v___x_706_;
goto v___jp_551_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_Elab_InfoTree_format(v_val_700_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Lean_MessageData_ofFormat(v_a_709_);
v___x_711_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_702_, v___x_710_, v___y_658_, v___y_667_);
v___y_578_ = v___y_659_;
v___y_579_ = v___y_655_;
v___y_580_ = v___y_660_;
v___y_581_ = v___y_657_;
v___y_582_ = v___y_663_;
v___y_583_ = v___y_664_;
v___y_584_ = v___x_698_;
v___y_585_ = v_a_669_;
v___y_586_ = v___y_667_;
v___y_587_ = v___y_658_;
v___y_588_ = v___x_711_;
goto v___jp_577_;
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
lean_dec(v___x_702_);
v_a_712_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_722_ == 0)
{
v___x_714_ = v___x_708_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_io_error_to_string(v_a_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 3);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Lean_MessageData_ofFormat(v___x_718_);
lean_inc(v___y_665_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_665_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___y_565_ = v___y_655_;
v___y_566_ = v___y_659_;
v___y_567_ = v___y_660_;
v___y_568_ = v___y_664_;
v___y_569_ = v___y_663_;
v___y_570_ = v___y_657_;
v___y_571_ = v___x_698_;
v___y_572_ = v_a_669_;
v___y_573_ = v___y_658_;
v___y_574_ = v___y_667_;
v_a_575_ = v___x_720_;
goto v___jp_564_;
}
}
}
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v___y_662_);
v___x_723_ = lean_box(0);
v___y_552_ = v___y_655_;
v___y_553_ = v___y_659_;
v___y_554_ = v___y_660_;
v___y_555_ = v___y_664_;
v___y_556_ = v___y_663_;
v___y_557_ = v___y_657_;
v___y_558_ = v___x_698_;
v___y_559_ = v_a_669_;
v___y_560_ = v___y_658_;
v___y_561_ = v___y_667_;
v_a_562_ = v___x_723_;
goto v___jp_551_;
}
}
else
{
lean_dec(v___y_662_);
v___y_578_ = v___y_659_;
v___y_579_ = v___y_655_;
v___y_580_ = v___y_660_;
v___y_581_ = v___y_657_;
v___y_582_ = v___y_663_;
v___y_583_ = v___y_664_;
v___y_584_ = v___x_698_;
v___y_585_ = v_a_669_;
v___y_586_ = v___y_667_;
v___y_587_ = v___y_658_;
v___y_588_ = v___x_699_;
goto v___jp_577_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
v_a_724_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_668_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_668_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
v_resetjp_734_:
{
lean_object* v_desc_737_; lean_object* v_diagnostics_738_; lean_object* v_infoTree_x3f_739_; lean_object* v_desc_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___x_834_; 
v_desc_737_ = lean_ctor_get(v_element_732_, 0);
lean_inc_ref(v_desc_737_);
v_diagnostics_738_ = lean_ctor_get(v_element_732_, 1);
lean_inc_ref(v_diagnostics_738_);
v_infoTree_x3f_739_ = lean_ctor_get(v_element_732_, 2);
lean_inc(v_infoTree_x3f_739_);
lean_dec_ref(v_element_732_);
v___x_834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_834_, 0, v_desc_737_);
switch(lean_obj_tag(v_range_x3f_526_))
{
case 0:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v_desc_741_ = v___x_836_;
v___y_742_ = v_a_528_;
v___y_743_ = v_a_529_;
goto v___jp_740_;
}
case 1:
{
lean_object* v_toCold_837_; lean_object* v_range_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_896_; 
v_toCold_837_ = lean_ctor_get(v_a_528_, 0);
v_range_838_ = lean_ctor_get(v_range_x3f_526_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_range_x3f_526_);
if (v_isSharedCheck_896_ == 0)
{
v___x_840_ = v_range_x3f_526_;
v_isShared_841_ = v_isSharedCheck_896_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_range_838_);
lean_dec(v_range_x3f_526_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_896_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_fileMap_842_; lean_object* v_start_843_; lean_object* v_stop_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_895_; 
v_fileMap_842_ = lean_ctor_get(v_toCold_837_, 1);
v_start_843_ = lean_ctor_get(v_range_838_, 0);
v_stop_844_ = lean_ctor_get(v_range_838_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_range_838_);
if (v_isSharedCheck_895_ == 0)
{
v___x_846_ = v_range_838_;
v_isShared_847_ = v_isSharedCheck_895_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_stop_844_);
lean_inc(v_start_843_);
lean_dec(v_range_838_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_895_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_line_849_; lean_object* v_column_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_894_; 
lean_inc_ref(v_fileMap_842_);
v___x_848_ = l_Lean_FileMap_toPosition(v_fileMap_842_, v_start_843_);
lean_dec(v_start_843_);
v_line_849_ = lean_ctor_get(v___x_848_, 0);
v_column_850_ = lean_ctor_get(v___x_848_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_894_ == 0)
{
v___x_852_ = v___x_848_;
v_isShared_853_ = v_isSharedCheck_894_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_column_850_);
lean_inc(v_line_849_);
lean_dec(v___x_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_894_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v_line_855_; lean_object* v_column_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_893_; 
lean_inc_ref(v_fileMap_842_);
v___x_854_ = l_Lean_FileMap_toPosition(v_fileMap_842_, v_stop_844_);
lean_dec(v_stop_844_);
v_line_855_ = lean_ctor_get(v___x_854_, 0);
v_column_856_ = lean_ctor_get(v___x_854_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_893_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_893_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_column_856_);
lean_inc(v_line_855_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_893_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_861_ = l_Nat_reprFast(v_line_849_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 3);
lean_ctor_set(v___x_840_, 0, v___x_861_);
v___x_863_ = v___x_840_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_892_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 5);
lean_ctor_set(v___x_858_, 1, v___x_863_);
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_865_ = v___x_858_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_891_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 5);
lean_ctor_set(v___x_852_, 1, v___x_866_);
lean_ctor_set(v___x_852_, 0, v___x_865_);
v___x_868_ = v___x_852_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_890_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = l_Nat_reprFast(v_column_850_);
v___x_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 5);
lean_ctor_set(v___x_846_, 1, v___x_870_);
lean_ctor_set(v___x_846_, 0, v___x_868_);
v___x_872_ = v___x_846_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_889_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Nat_reprFast(v_line_855_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_860_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_866_);
v___x_881_ = l_Nat_reprFast(v_column_856_);
v___x_882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_880_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_873_);
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_876_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_834_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v_desc_741_ = v___x_888_;
v___y_742_ = v_a_528_;
v___y_743_ = v_a_529_;
goto v___jp_740_;
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
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_834_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v_desc_741_ = v___x_898_;
v___y_742_ = v_a_528_;
v___y_743_ = v_a_529_;
goto v___jp_740_;
}
}
v___jp_740_:
{
lean_object* v_msgLog_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_832_; 
v_msgLog_744_ = lean_ctor_get(v_diagnostics_738_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_diagnostics_738_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_diagnostics_738_, 1);
lean_dec(v_unused_833_);
v___x_746_ = v_diagnostics_738_;
v_isShared_747_ = v_isSharedCheck_832_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_msgLog_744_);
lean_dec(v_diagnostics_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_832_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = l_Lean_MessageLog_toList(v_msgLog_744_);
lean_dec_ref(v_msgLog_744_);
v___x_749_ = lean_box(0);
v___x_750_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_748_, v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_toCold_751_; lean_object* v_options_752_; lean_object* v_a_753_; lean_object* v_ref_754_; lean_object* v_inheritedTraceOptions_755_; uint8_t v_hasTrace_756_; lean_object* v___x_757_; 
v_toCold_751_ = lean_ctor_get(v___y_742_, 0);
v_options_752_ = lean_ctor_get(v_toCold_751_, 2);
v_a_753_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_750_, 1);
v_ref_754_ = lean_ctor_get(v___y_742_, 2);
v_inheritedTraceOptions_755_ = lean_ctor_get(v_toCold_751_, 11);
v_hasTrace_756_ = lean_ctor_get_uint8(v_options_752_, sizeof(void*)*1);
v___x_757_ = lean_array_to_list(v_children_733_);
if (v_hasTrace_756_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_a_753_);
lean_del_object(v___x_746_);
lean_dec(v_desc_741_);
lean_dec(v_infoTree_x3f_739_);
lean_del_object(v___x_735_);
v___x_758_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_757_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_767_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_box(0);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
return v___x_758_;
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_769_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_770_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_769_, v_a_753_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 5);
lean_ctor_set(v___x_746_, 1, v___x_770_);
lean_ctor_set(v___x_746_, 0, v_desc_741_);
v___x_772_ = v___x_746_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_desc_741_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_823_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___f_773_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_773_, 0, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_775_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_776_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_755_, v_options_752_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = l_Lean_trace_profiler;
v___x_779_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_752_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___f_773_);
v___x_780_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_757_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_780_, 0);
lean_dec(v_unused_822_);
v___x_782_ = v___x_780_;
v_isShared_783_ = v_isSharedCheck_821_;
goto v_resetjp_781_;
}
else
{
lean_dec(v___x_780_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_821_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
if (lean_obj_tag(v_infoTree_x3f_739_) == 1)
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_816_; 
v_val_784_ = lean_ctor_get(v_infoTree_x3f_739_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_infoTree_x3f_739_);
if (v_isSharedCheck_816_ == 0)
{
v___x_786_ = v_infoTree_x3f_739_;
v_isShared_787_ = v_isSharedCheck_816_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v_infoTree_x3f_739_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_816_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_789_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_755_, v_options_752_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_del_object(v___x_786_);
lean_dec(v_val_784_);
lean_del_object(v___x_735_);
v___x_791_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_791_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_782_);
v___x_795_ = lean_box(0);
v___x_796_ = l_Lean_Elab_InfoTree_format(v_val_784_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_786_);
lean_del_object(v___x_735_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_MessageData_ofFormat(v_a_797_);
v___x_799_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_788_, v___x_798_, v___y_742_, v___y_743_);
return v___x_799_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_815_; 
v_a_800_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_802_ = v___x_796_;
v_isShared_803_ = v_isSharedCheck_815_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_796_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_815_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_io_error_to_string(v_a_800_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 3);
lean_ctor_set(v___x_786_, 0, v___x_804_);
v___x_806_ = v___x_786_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_814_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = l_Lean_MessageData_ofFormat(v___x_806_);
lean_inc(v_ref_754_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_807_);
lean_ctor_set(v___x_735_, 0, v_ref_754_);
v___x_809_ = v___x_735_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_ref_754_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_809_);
v___x_811_ = v___x_802_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
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
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v_infoTree_x3f_739_);
lean_del_object(v___x_735_);
v___x_817_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_817_);
v___x_819_ = v___x_782_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_739_);
lean_del_object(v___x_735_);
return v___x_780_;
}
}
else
{
lean_del_object(v___x_735_);
v___y_655_ = v_hasTrace_756_;
v___y_656_ = v___x_768_;
v___y_657_ = v___x_777_;
v___y_658_ = v___y_742_;
v___y_659_ = v_options_752_;
v___y_660_ = v___f_773_;
v___y_661_ = v___x_757_;
v___y_662_ = v_infoTree_x3f_739_;
v___y_663_ = v___x_775_;
v___y_664_ = v___x_774_;
v___y_665_ = v_ref_754_;
v___y_666_ = v_inheritedTraceOptions_755_;
v___y_667_ = v___y_743_;
goto v___jp_654_;
}
}
else
{
lean_del_object(v___x_735_);
v___y_655_ = v_hasTrace_756_;
v___y_656_ = v___x_768_;
v___y_657_ = v___x_777_;
v___y_658_ = v___y_742_;
v___y_659_ = v_options_752_;
v___y_660_ = v___f_773_;
v___y_661_ = v___x_757_;
v___y_662_ = v_infoTree_x3f_739_;
v___y_663_ = v___x_775_;
v___y_664_ = v___x_774_;
v___y_665_ = v_ref_754_;
v___y_666_ = v_inheritedTraceOptions_755_;
v___y_667_ = v___y_743_;
goto v___jp_654_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_del_object(v___x_746_);
lean_dec(v_desc_741_);
lean_dec(v_infoTree_x3f_739_);
lean_del_object(v___x_735_);
lean_dec_ref(v_children_733_);
v_a_824_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_750_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_750_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_x3f_526_ = stack[0].m_obj;
lean_object* v_s_527_ = stack[1].m_obj;
lean_object* v_a_528_ = stack[2].m_obj;
lean_object* v_a_529_ = stack[3].m_obj;
lean_object* v_res_900_;
v_res_900_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_526_, v_s_527_, v_a_528_, v_a_529_);
stack->m_obj
 = v_res_900_;
}
lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
if (lean_obj_tag(v_as_901_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_box(0);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v_head_907_; lean_object* v_tail_908_; lean_object* v_reportingRange_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_head_907_ = lean_ctor_get(v_as_901_, 0);
lean_inc(v_head_907_);
v_tail_908_ = lean_ctor_get(v_as_901_, 1);
lean_inc(v_tail_908_);
lean_dec_ref_known(v_as_901_, 2);
v_reportingRange_909_ = lean_ctor_get(v_head_907_, 1);
lean_inc(v_reportingRange_909_);
v___x_910_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_907_);
v___x_911_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_909_, v___x_910_, v___y_902_, v___y_903_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec_ref_known(v___x_911_, 1);
v_as_901_ = v_tail_908_;
goto _start;
}
else
{
lean_dec(v_tail_908_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_901_ = stack[0].m_obj;
lean_object* v___y_902_ = stack[1].m_obj;
lean_object* v___y_903_ = stack[2].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_901_, v___y_902_, v___y_903_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_919_, lean_object* v_s_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_919_, v_s_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_924_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_925_, v_x_926_);
return v___x_930_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_925_ = stack[0].m_obj;
lean_object* v_x_926_ = stack[1].m_obj;
lean_object* v___y_927_ = stack[2].m_obj;
lean_object* v___y_928_ = stack[3].m_obj;
lean_object* v_res_931_;
v_res_931_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_925_, v_x_926_, v___y_927_, v___y_928_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_932_, v_x_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_937_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_938_, lean_object* v_x_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_939_);
return v___x_943_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_939_ = stack[1].m_obj;
lean_object* v___y_940_ = stack[2].m_obj;
lean_object* v___y_941_ = stack[3].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_box(0), v_x_939_, v___y_940_, v___y_941_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_945_, lean_object* v_x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_945_, v_x_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_950_;
}
}
lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_box(2);
v___x_956_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_955_, v_s_951_, v_a_952_, v_a_953_);
return v___x_956_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_trace_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_951_ = stack[0].m_obj;
lean_object* v_a_952_ = stack[1].m_obj;
lean_object* v_a_953_ = stack[2].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_Lean_Language_SnapshotTree_trace(v_s_951_, v_a_952_, v_a_953_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Language_SnapshotTree_trace(v_s_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_962_;
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

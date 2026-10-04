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
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set(v___x_88_, 3, v___x_87_);
lean_ctor_set(v___x_88_, 4, v___x_86_);
lean_ctor_set(v___x_88_, 5, v___x_86_);
lean_ctor_set(v___x_88_, 6, v___x_86_);
lean_ctor_set(v___x_88_, 7, v___x_86_);
lean_ctor_set(v___x_88_, 8, v___x_86_);
lean_ctor_set(v___x_88_, 9, v___x_86_);
lean_ctor_set(v___x_88_, 10, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(32u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = ((size_t)5ULL);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
v___x_97_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_93_);
lean_ctor_set(v___x_97_, 3, v___x_93_);
lean_ctor_set_usize(v___x_97_, 4, v___x_92_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_box(1);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v_toCold_107_; lean_object* v_env_108_; lean_object* v_options_109_; uint8_t v___x_110_; lean_object* v_env_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_toCold_107_ = lean_ctor_get(v___y_103_, 0);
v_env_108_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_106_);
v_options_109_ = lean_ctor_get(v_toCold_107_, 2);
v___x_110_ = 0;
v_env_111_ = l_Lean_Environment_setRecordingDeps(v_env_108_, v___x_110_);
v___x_112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_109_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_111_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_ctor_set(v___x_114_, 3, v_options_109_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_102_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_121_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_122_; double v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_float_of_nat(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_127_, lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_ref_132_; lean_object* v___x_133_; lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_179_; 
v_ref_132_ = lean_ctor_get(v___y_129_, 2);
v___x_133_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_128_, v___y_129_, v___y_130_);
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_179_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_179_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_179_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v_traceState_139_; lean_object* v_env_140_; lean_object* v_nextMacroScope_141_; lean_object* v_ngen_142_; lean_object* v_auxDeclNGen_143_; lean_object* v_cache_144_; lean_object* v_recordedDeps_145_; lean_object* v_messages_146_; lean_object* v_infoState_147_; lean_object* v_snapshotTasks_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_178_; 
v___x_138_ = lean_st_ref_take(v___y_130_);
v_traceState_139_ = lean_ctor_get(v___x_138_, 4);
v_env_140_ = lean_ctor_get(v___x_138_, 0);
v_nextMacroScope_141_ = lean_ctor_get(v___x_138_, 1);
v_ngen_142_ = lean_ctor_get(v___x_138_, 2);
v_auxDeclNGen_143_ = lean_ctor_get(v___x_138_, 3);
v_cache_144_ = lean_ctor_get(v___x_138_, 5);
v_recordedDeps_145_ = lean_ctor_get(v___x_138_, 6);
v_messages_146_ = lean_ctor_get(v___x_138_, 7);
v_infoState_147_ = lean_ctor_get(v___x_138_, 8);
v_snapshotTasks_148_ = lean_ctor_get(v___x_138_, 9);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_178_ == 0)
{
v___x_150_ = v___x_138_;
v_isShared_151_ = v_isSharedCheck_178_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_snapshotTasks_148_);
lean_inc(v_infoState_147_);
lean_inc(v_messages_146_);
lean_inc(v_recordedDeps_145_);
lean_inc(v_cache_144_);
lean_inc(v_traceState_139_);
lean_inc(v_auxDeclNGen_143_);
lean_inc(v_ngen_142_);
lean_inc(v_nextMacroScope_141_);
lean_inc(v_env_140_);
lean_dec(v___x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_178_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
uint64_t v_tid_152_; lean_object* v_traces_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_177_; 
v_tid_152_ = lean_ctor_get_uint64(v_traceState_139_, sizeof(void*)*1);
v_traces_153_ = lean_ctor_get(v_traceState_139_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v_traceState_139_);
if (v_isSharedCheck_177_ == 0)
{
v___x_155_ = v_traceState_139_;
v_isShared_156_ = v_isSharedCheck_177_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_traces_153_);
lean_dec(v_traceState_139_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_177_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; double v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_box(0);
v___x_159_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_160_ = 0;
v___x_161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_162_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_162_, 0, v_cls_127_);
lean_ctor_set(v___x_162_, 1, v___x_158_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
lean_ctor_set_float(v___x_162_, sizeof(void*)*3, v___x_159_);
lean_ctor_set_float(v___x_162_, sizeof(void*)*3 + 8, v___x_159_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*3 + 16, v___x_160_);
v___x_163_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_164_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v_a_134_);
lean_ctor_set(v___x_164_, 2, v___x_163_);
lean_inc(v_ref_132_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_ref_132_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_PersistentArray_push___redArg(v_traces_153_, v___x_165_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_166_);
v___x_168_ = v___x_155_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_166_);
lean_ctor_set_uint64(v_reuseFailAlloc_176_, sizeof(void*)*1, v_tid_152_);
v___x_168_ = v_reuseFailAlloc_176_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v___x_168_);
v___x_170_ = v___x_150_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_env_140_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_nextMacroScope_141_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_ngen_142_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_auxDeclNGen_143_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 5, v_cache_144_);
lean_ctor_set(v_reuseFailAlloc_175_, 6, v_recordedDeps_145_);
lean_ctor_set(v_reuseFailAlloc_175_, 7, v_messages_146_);
lean_ctor_set(v_reuseFailAlloc_175_, 8, v_infoState_147_);
lean_ctor_set(v_reuseFailAlloc_175_, 9, v_snapshotTasks_148_);
v___x_170_ = v_reuseFailAlloc_175_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_st_ref_put(v___y_130_, v___x_170_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_157_);
v___x_173_ = v___x_136_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_157_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_180_, v_msg_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_dec(v_pre_186_);
return v_x_187_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_head_189_ = lean_ctor_get(v_x_188_, 0);
v_tail_190_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v_x_188_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_tail_190_);
lean_inc(v_head_189_);
lean_dec(v_x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
lean_inc(v_pre_186_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 5);
lean_ctor_set(v___x_192_, 1, v_pre_186_);
lean_ctor_set(v___x_192_, 0, v_x_187_);
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_x_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_pre_186_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_196_, 0, v_head_189_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v_x_187_ = v___x_197_;
v_x_188_ = v_tail_190_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v___x_203_; 
lean_dec(v_pre_201_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_head_204_; lean_object* v_tail_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_214_; 
v_head_204_ = lean_ctor_get(v_x_202_, 0);
v_tail_205_ = lean_ctor_get(v_x_202_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_214_ == 0)
{
v___x_207_ = v_x_202_;
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_tail_205_);
lean_inc(v_head_204_);
lean_dec(v_x_202_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_209_, 0, v_head_204_);
lean_inc(v_pre_201_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 5);
lean_ctor_set(v___x_207_, 1, v___x_209_);
lean_ctor_set(v___x_207_, 0, v_pre_201_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_pre_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_201_, v___x_211_, v_tail_205_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = l_List_reverse___redArg(v_x_216_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v_head_220_ = lean_ctor_get(v_x_215_, 0);
v_tail_221_ = lean_ctor_get(v_x_215_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v_x_215_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_tail_221_);
lean_inc(v_head_220_);
lean_dec(v_x_215_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = 0;
v___x_226_ = l_Lean_Message_toString(v_head_220_, v___x_225_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_x_216_);
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_x_216_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_x_215_ = v_tail_221_;
v_x_216_ = v___x_228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_232_, v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v_x_236_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v_x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 1);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v_x_236_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v_x_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 0);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_257_, lean_object* v_opt_258_){
_start:
{
lean_object* v_name_259_; lean_object* v_defValue_260_; lean_object* v_map_261_; lean_object* v___x_262_; 
v_name_259_ = lean_ctor_get(v_opt_258_, 0);
v_defValue_260_ = lean_ctor_get(v_opt_258_, 1);
v_map_261_ = lean_ctor_get(v_opts_257_, 0);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_261_, v_name_259_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_inc(v_defValue_260_);
return v_defValue_260_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v___x_262_, 1);
if (lean_obj_tag(v_val_263_) == 3)
{
lean_object* v_v_264_; 
v_v_264_ = lean_ctor_get(v_val_263_, 0);
lean_inc(v_v_264_);
lean_dec_ref_known(v_val_263_, 1);
return v_v_264_;
}
else
{
lean_dec(v_val_263_);
lean_inc(v_defValue_260_);
return v_defValue_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_265_, lean_object* v_opt_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_265_, v_opt_266_);
lean_dec_ref(v_opt_266_);
lean_dec_ref(v_opts_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_268_, size_t v_i_269_, lean_object* v_bs_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_lt(v_i_269_, v_sz_268_);
if (v___x_271_ == 0)
{
return v_bs_270_;
}
else
{
lean_object* v_v_272_; lean_object* v_msg_273_; lean_object* v___x_274_; lean_object* v_bs_x27_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v_v_272_ = lean_array_uget_borrowed(v_bs_270_, v_i_269_);
v_msg_273_ = lean_ctor_get(v_v_272_, 1);
lean_inc_ref(v_msg_273_);
v___x_274_ = lean_unsigned_to_nat(0u);
v_bs_x27_275_ = lean_array_uset(v_bs_270_, v_i_269_, v___x_274_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_269_, v___x_276_);
v___x_278_ = lean_array_uset(v_bs_x27_275_, v_i_269_, v_msg_273_);
v_i_269_ = v___x_277_;
v_bs_270_ = v___x_278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_280_, lean_object* v_i_281_, lean_object* v_bs_282_){
_start:
{
size_t v_sz_boxed_283_; size_t v_i_boxed_284_; lean_object* v_res_285_; 
v_sz_boxed_283_ = lean_unbox_usize(v_sz_280_);
lean_dec(v_sz_280_);
v_i_boxed_284_ = lean_unbox_usize(v_i_281_);
lean_dec(v_i_281_);
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_283_, v_i_boxed_284_, v_bs_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_286_, lean_object* v_data_287_, lean_object* v_ref_288_, lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_toCold_293_; lean_object* v_currRecDepth_294_; lean_object* v_ref_295_; uint16_t v_optionFlags_296_; uint8_t v_suppressElabErrors_297_; uint8_t v_isRecordingDeps_298_; lean_object* v_ref_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_traceState_302_; lean_object* v_traces_303_; lean_object* v___x_304_; size_t v_sz_305_; size_t v___x_306_; lean_object* v___x_307_; lean_object* v_msg_308_; lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_348_; 
v_toCold_293_ = lean_ctor_get(v___y_290_, 0);
v_currRecDepth_294_ = lean_ctor_get(v___y_290_, 1);
v_ref_295_ = lean_ctor_get(v___y_290_, 2);
v_optionFlags_296_ = lean_ctor_get_uint16(v___y_290_, sizeof(void*)*3);
v_suppressElabErrors_297_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*3 + 2);
v_isRecordingDeps_298_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*3 + 3);
v_ref_299_ = l_Lean_replaceRef(v_ref_288_, v_ref_295_);
lean_inc(v_currRecDepth_294_);
lean_inc_ref(v_toCold_293_);
v___x_300_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_300_, 0, v_toCold_293_);
lean_ctor_set(v___x_300_, 1, v_currRecDepth_294_);
lean_ctor_set(v___x_300_, 2, v_ref_299_);
lean_ctor_set_uint16(v___x_300_, sizeof(void*)*3, v_optionFlags_296_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*3 + 2, v_suppressElabErrors_297_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*3 + 3, v_isRecordingDeps_298_);
v___x_301_ = lean_st_ref_get(v___y_291_);
v_traceState_302_ = lean_ctor_get(v___x_301_, 4);
lean_inc_ref(v_traceState_302_);
lean_dec(v___x_301_);
v_traces_303_ = lean_ctor_get(v_traceState_302_, 0);
lean_inc_ref(v_traces_303_);
lean_dec_ref(v_traceState_302_);
v___x_304_ = l_Lean_PersistentArray_toArray___redArg(v_traces_303_);
lean_dec_ref(v_traces_303_);
v_sz_305_ = lean_array_size(v___x_304_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_305_, v___x_306_, v___x_304_);
v_msg_308_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_308_, 0, v_data_287_);
lean_ctor_set(v_msg_308_, 1, v_msg_289_);
lean_ctor_set(v_msg_308_, 2, v___x_307_);
v___x_309_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_308_, v___x_300_, v___y_291_);
lean_dec_ref_known(v___x_300_, 3);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_348_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_348_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_348_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v_traceState_315_; lean_object* v_env_316_; lean_object* v_nextMacroScope_317_; lean_object* v_ngen_318_; lean_object* v_auxDeclNGen_319_; lean_object* v_cache_320_; lean_object* v_recordedDeps_321_; lean_object* v_messages_322_; lean_object* v_infoState_323_; lean_object* v_snapshotTasks_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_347_; 
v___x_314_ = lean_st_ref_take(v___y_291_);
v_traceState_315_ = lean_ctor_get(v___x_314_, 4);
v_env_316_ = lean_ctor_get(v___x_314_, 0);
v_nextMacroScope_317_ = lean_ctor_get(v___x_314_, 1);
v_ngen_318_ = lean_ctor_get(v___x_314_, 2);
v_auxDeclNGen_319_ = lean_ctor_get(v___x_314_, 3);
v_cache_320_ = lean_ctor_get(v___x_314_, 5);
v_recordedDeps_321_ = lean_ctor_get(v___x_314_, 6);
v_messages_322_ = lean_ctor_get(v___x_314_, 7);
v_infoState_323_ = lean_ctor_get(v___x_314_, 8);
v_snapshotTasks_324_ = lean_ctor_get(v___x_314_, 9);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_347_ == 0)
{
v___x_326_ = v___x_314_;
v_isShared_327_ = v_isSharedCheck_347_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snapshotTasks_324_);
lean_inc(v_infoState_323_);
lean_inc(v_messages_322_);
lean_inc(v_recordedDeps_321_);
lean_inc(v_cache_320_);
lean_inc(v_traceState_315_);
lean_inc(v_auxDeclNGen_319_);
lean_inc(v_ngen_318_);
lean_inc(v_nextMacroScope_317_);
lean_inc(v_env_316_);
lean_dec(v___x_314_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_347_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint64_t v_tid_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_345_; 
v_tid_328_ = lean_ctor_get_uint64(v_traceState_315_, sizeof(void*)*1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_traceState_315_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_traceState_315_, 0);
lean_dec(v_unused_346_);
v___x_330_ = v_traceState_315_;
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_traceState_315_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_ref_288_);
lean_ctor_set(v___x_333_, 1, v_a_310_);
v___x_334_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_286_, v___x_333_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_334_);
v___x_336_ = v___x_330_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_334_);
lean_ctor_set_uint64(v_reuseFailAlloc_344_, sizeof(void*)*1, v_tid_328_);
v___x_336_ = v_reuseFailAlloc_344_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 4, v___x_336_);
v___x_338_ = v___x_326_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_env_316_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_nextMacroScope_317_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_ngen_318_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_auxDeclNGen_319_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v_cache_320_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_recordedDeps_321_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_messages_322_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 9, v_snapshotTasks_324_);
v___x_338_ = v_reuseFailAlloc_343_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_st_ref_put(v___y_291_, v___x_338_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_332_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_332_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_349_, lean_object* v_data_350_, lean_object* v_ref_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_349_, v_data_350_, v_ref_351_, v_msg_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_357_){
_start:
{
if (lean_obj_tag(v_e_357_) == 0)
{
uint8_t v___x_358_; 
v___x_358_ = 2;
return v___x_358_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_360_);
lean_dec_ref(v_e_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_366_; double v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(1000u);
v___x_367_ = lean_float_of_nat(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_368_, uint8_t v_collapsed_369_, lean_object* v_tag_370_, lean_object* v_opts_371_, uint8_t v_clsEnabled_372_, lean_object* v_oldTraces_373_, lean_object* v_msg_374_, lean_object* v_resStartStop_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v_data_384_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___y_392_; lean_object* v_a_393_; uint8_t v___y_408_; double v___y_440_; 
v_fst_379_ = lean_ctor_get(v_resStartStop_375_, 0);
lean_inc(v_fst_379_);
v_snd_380_ = lean_ctor_get(v_resStartStop_375_, 1);
lean_inc(v_snd_380_);
lean_dec_ref(v_resStartStop_375_);
v_fst_387_ = lean_ctor_get(v_snd_380_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v_snd_380_, 1);
lean_inc(v_snd_388_);
lean_dec(v_snd_380_);
v___x_389_ = l_Lean_trace_profiler;
v___x_390_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_371_, v___x_389_);
if (v___x_390_ == 0)
{
v___y_408_ = v___x_390_;
goto v___jp_407_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = l_Lean_trace_profiler_useHeartbeats;
v___x_446_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_371_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; double v___x_449_; double v___x_450_; double v___x_451_; 
v___x_447_ = l_Lean_trace_profiler_threshold;
v___x_448_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_371_, v___x_447_);
v___x_449_ = lean_float_of_nat(v___x_448_);
v___x_450_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_451_ = lean_float_div(v___x_449_, v___x_450_);
v___y_440_ = v___x_451_;
goto v___jp_439_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; double v___x_454_; 
v___x_452_ = l_Lean_trace_profiler_threshold;
v___x_453_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_371_, v___x_452_);
v___x_454_ = lean_float_of_nat(v___x_453_);
v___y_440_ = v___x_454_;
goto v___jp_439_;
}
}
v___jp_381_:
{
lean_object* v___x_385_; 
lean_inc(v___y_382_);
v___x_385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_373_, v_data_384_, v___y_382_, v___y_383_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec_ref_known(v___x_385_, 1);
v___x_386_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_379_);
return v___x_386_;
}
else
{
lean_dec(v_fst_379_);
return v___x_385_;
}
}
v___jp_391_:
{
uint8_t v_result_394_; lean_object* v___x_395_; lean_object* v___x_396_; double v___x_397_; lean_object* v_data_398_; 
v_result_394_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_379_);
v___x_395_ = lean_box(v_result_394_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___x_397_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_370_);
lean_inc_ref(v___x_396_);
lean_inc(v_cls_368_);
v_data_398_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_398_, 0, v_cls_368_);
lean_ctor_set(v_data_398_, 1, v___x_396_);
lean_ctor_set(v_data_398_, 2, v_tag_370_);
lean_ctor_set_float(v_data_398_, sizeof(void*)*3, v___x_397_);
lean_ctor_set_float(v_data_398_, sizeof(void*)*3 + 8, v___x_397_);
lean_ctor_set_uint8(v_data_398_, sizeof(void*)*3 + 16, v_collapsed_369_);
if (v___x_390_ == 0)
{
lean_dec_ref_known(v___x_396_, 1);
lean_dec(v_snd_388_);
lean_dec(v_fst_387_);
lean_dec_ref(v_tag_370_);
lean_dec(v_cls_368_);
v___y_382_ = v___y_392_;
v___y_383_ = v_a_393_;
v_data_384_ = v_data_398_;
goto v___jp_381_;
}
else
{
lean_object* v_data_399_; double v___x_400_; double v___x_401_; 
lean_dec_ref_known(v_data_398_, 3);
v_data_399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_399_, 0, v_cls_368_);
lean_ctor_set(v_data_399_, 1, v___x_396_);
lean_ctor_set(v_data_399_, 2, v_tag_370_);
v___x_400_ = lean_unbox_float(v_fst_387_);
lean_dec(v_fst_387_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3, v___x_400_);
v___x_401_ = lean_unbox_float(v_snd_388_);
lean_dec(v_snd_388_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3 + 8, v___x_401_);
lean_ctor_set_uint8(v_data_399_, sizeof(void*)*3 + 16, v_collapsed_369_);
v___y_382_ = v___y_392_;
v___y_383_ = v_a_393_;
v_data_384_ = v_data_399_;
goto v___jp_381_;
}
}
v___jp_402_:
{
lean_object* v_ref_403_; lean_object* v___x_404_; 
v_ref_403_ = lean_ctor_get(v___y_376_, 2);
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
lean_inc(v_fst_379_);
v___x_404_ = lean_apply_4(v_msg_374_, v_fst_379_, v___y_376_, v___y_377_, lean_box(0));
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v___y_392_ = v_ref_403_;
v_a_393_ = v_a_405_;
goto v___jp_391_;
}
else
{
lean_object* v___x_406_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_392_ = v_ref_403_;
v_a_393_ = v___x_406_;
goto v___jp_391_;
}
}
v___jp_407_:
{
if (v_clsEnabled_372_ == 0)
{
if (v___y_408_ == 0)
{
lean_object* v___x_409_; lean_object* v_traceState_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_cache_415_; lean_object* v_recordedDeps_416_; lean_object* v_messages_417_; lean_object* v_infoState_418_; lean_object* v_snapshotTasks_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_438_; 
lean_dec(v_snd_388_);
lean_dec(v_fst_387_);
lean_dec_ref(v_msg_374_);
lean_dec_ref(v_tag_370_);
lean_dec(v_cls_368_);
v___x_409_ = lean_st_ref_take(v___y_377_);
v_traceState_410_ = lean_ctor_get(v___x_409_, 4);
v_env_411_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_409_, 1);
v_ngen_413_ = lean_ctor_get(v___x_409_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_409_, 3);
v_cache_415_ = lean_ctor_get(v___x_409_, 5);
v_recordedDeps_416_ = lean_ctor_get(v___x_409_, 6);
v_messages_417_ = lean_ctor_get(v___x_409_, 7);
v_infoState_418_ = lean_ctor_get(v___x_409_, 8);
v_snapshotTasks_419_ = lean_ctor_get(v___x_409_, 9);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_438_ == 0)
{
v___x_421_ = v___x_409_;
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snapshotTasks_419_);
lean_inc(v_infoState_418_);
lean_inc(v_messages_417_);
lean_inc(v_recordedDeps_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint64_t v_tid_423_; lean_object* v_traces_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_437_; 
v_tid_423_ = lean_ctor_get_uint64(v_traceState_410_, sizeof(void*)*1);
v_traces_424_ = lean_ctor_get(v_traceState_410_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_traceState_410_);
if (v_isSharedCheck_437_ == 0)
{
v___x_426_ = v_traceState_410_;
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_traces_424_);
lean_dec(v_traceState_410_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_373_, v_traces_424_);
lean_dec_ref(v_traces_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_428_);
lean_ctor_set_uint64(v_reuseFailAlloc_436_, sizeof(void*)*1, v_tid_423_);
v___x_430_ = v_reuseFailAlloc_436_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 4, v___x_430_);
v___x_432_ = v___x_421_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_env_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_recordedDeps_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_messages_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_infoState_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_snapshotTasks_419_);
v___x_432_ = v_reuseFailAlloc_435_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_st_ref_put(v___y_377_, v___x_432_);
v___x_434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_379_);
return v___x_434_;
}
}
}
}
}
else
{
goto v___jp_402_;
}
}
else
{
goto v___jp_402_;
}
}
v___jp_439_:
{
double v___x_441_; double v___x_442_; double v___x_443_; uint8_t v___x_444_; 
v___x_441_ = lean_unbox_float(v_snd_388_);
v___x_442_ = lean_unbox_float(v_fst_387_);
v___x_443_ = lean_float_sub(v___x_441_, v___x_442_);
v___x_444_ = lean_float_decLt(v___y_440_, v___x_443_);
v___y_408_ = v___x_444_;
goto v___jp_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_455_, lean_object* v_collapsed_456_, lean_object* v_tag_457_, lean_object* v_opts_458_, lean_object* v_clsEnabled_459_, lean_object* v_oldTraces_460_, lean_object* v_msg_461_, lean_object* v_resStartStop_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_collapsed_boxed_466_; uint8_t v_clsEnabled_boxed_467_; lean_object* v_res_468_; 
v_collapsed_boxed_466_ = lean_unbox(v_collapsed_456_);
v_clsEnabled_boxed_467_ = lean_unbox(v_clsEnabled_459_);
v_res_468_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_455_, v_collapsed_boxed_466_, v_tag_457_, v_opts_458_, v_clsEnabled_boxed_467_, v_oldTraces_460_, v_msg_461_, v_resStartStop_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_opts_458_);
return v_res_468_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_469_; double v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(1000000000u);
v___x_470_ = lean_float_of_nat(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_484_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_485_ = l_Lean_Name_append(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_490_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_491_ = l_Lean_Name_append(v___x_490_, v___x_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_513_, lean_object* v_s_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___y_519_; uint8_t v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v_a_529_; lean_object* v___y_539_; uint8_t v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v_a_549_; lean_object* v___y_552_; uint8_t v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v_a_562_; lean_object* v___y_565_; uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint8_t v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_579_; uint8_t v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v_a_589_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v_a_612_; lean_object* v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; lean_object* v_a_625_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v_element_719_; lean_object* v_children_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_886_; 
v_element_719_ = lean_ctor_get(v_s_514_, 0);
v_children_720_ = lean_ctor_get(v_s_514_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_s_514_);
if (v_isSharedCheck_886_ == 0)
{
v___x_722_ = v_s_514_;
v_isShared_723_ = v_isSharedCheck_886_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_children_720_);
lean_inc(v_element_719_);
lean_dec(v_s_514_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_886_;
goto v_resetjp_721_;
}
v___jp_518_:
{
lean_object* v___x_530_; double v___x_531_; double v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_530_ = lean_io_get_num_heartbeats();
v___x_531_ = lean_float_of_nat(v___y_528_);
v___x_532_ = lean_float_of_nat(v___x_530_);
v___x_533_ = lean_box_float(v___x_531_);
v___x_534_ = lean_box_float(v___x_532_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_529_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_526_);
v___x_537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_526_, v___y_520_, v___y_523_, v___y_521_, v___y_527_, v___y_525_, v___y_524_, v___x_536_, v___y_519_, v___y_522_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v_a_549_);
v___y_519_ = v___y_539_;
v___y_520_ = v___y_540_;
v___y_521_ = v___y_541_;
v___y_522_ = v___y_543_;
v___y_523_ = v___y_542_;
v___y_524_ = v___y_544_;
v___y_525_ = v___y_546_;
v___y_526_ = v___y_545_;
v___y_527_ = v___y_548_;
v___y_528_ = v___y_547_;
v_a_529_ = v___x_550_;
goto v___jp_518_;
}
v___jp_551_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_a_562_);
v___y_519_ = v___y_552_;
v___y_520_ = v___y_553_;
v___y_521_ = v___y_554_;
v___y_522_ = v___y_556_;
v___y_523_ = v___y_555_;
v___y_524_ = v___y_557_;
v___y_525_ = v___y_559_;
v___y_526_ = v___y_558_;
v___y_527_ = v___y_561_;
v___y_528_ = v___y_560_;
v_a_529_ = v___x_563_;
goto v___jp_518_;
}
v___jp_564_:
{
if (lean_obj_tag(v___y_575_) == 0)
{
lean_object* v_a_576_; 
v_a_576_ = lean_ctor_get(v___y_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___y_575_, 1);
v___y_539_ = v___y_565_;
v___y_540_ = v___y_566_;
v___y_541_ = v___y_567_;
v___y_542_ = v___y_569_;
v___y_543_ = v___y_568_;
v___y_544_ = v___y_570_;
v___y_545_ = v___y_572_;
v___y_546_ = v___y_571_;
v___y_547_ = v___y_574_;
v___y_548_ = v___y_573_;
v_a_549_ = v_a_576_;
goto v___jp_538_;
}
else
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v___y_575_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___y_575_, 1);
v___y_552_ = v___y_565_;
v___y_553_ = v___y_566_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_569_;
v___y_556_ = v___y_568_;
v___y_557_ = v___y_570_;
v___y_558_ = v___y_572_;
v___y_559_ = v___y_571_;
v___y_560_ = v___y_574_;
v___y_561_ = v___y_573_;
v_a_562_ = v_a_577_;
goto v___jp_551_;
}
}
v___jp_578_:
{
lean_object* v___x_590_; double v___x_591_; double v___x_592_; double v___x_593_; double v___x_594_; double v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_590_ = lean_io_mono_nanos_now();
v___x_591_ = lean_float_of_nat(v___y_585_);
v___x_592_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_593_ = lean_float_div(v___x_591_, v___x_592_);
v___x_594_ = lean_float_of_nat(v___x_590_);
v___x_595_ = lean_float_div(v___x_594_, v___x_592_);
v___x_596_ = lean_box_float(v___x_593_);
v___x_597_ = lean_box_float(v___x_595_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_589_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_587_);
v___x_600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_587_, v___y_580_, v___y_583_, v___y_581_, v___y_588_, v___y_586_, v___y_584_, v___x_599_, v___y_579_, v___y_582_);
return v___x_600_;
}
v___jp_601_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_a_612_);
v___y_579_ = v___y_602_;
v___y_580_ = v___y_603_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_606_;
v___y_583_ = v___y_605_;
v___y_584_ = v___y_608_;
v___y_585_ = v___y_607_;
v___y_586_ = v___y_610_;
v___y_587_ = v___y_609_;
v___y_588_ = v___y_611_;
v_a_589_ = v___x_613_;
goto v___jp_578_;
}
v___jp_614_:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_a_625_);
v___y_579_ = v___y_615_;
v___y_580_ = v___y_616_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_619_;
v___y_583_ = v___y_618_;
v___y_584_ = v___y_621_;
v___y_585_ = v___y_620_;
v___y_586_ = v___y_623_;
v___y_587_ = v___y_622_;
v___y_588_ = v___y_624_;
v_a_589_ = v___x_626_;
goto v___jp_578_;
}
v___jp_627_:
{
if (lean_obj_tag(v___y_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___y_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___y_638_, 1);
v___y_602_ = v___y_628_;
v___y_603_ = v___y_629_;
v___y_604_ = v___y_630_;
v___y_605_ = v___y_632_;
v___y_606_ = v___y_631_;
v___y_607_ = v___y_634_;
v___y_608_ = v___y_633_;
v___y_609_ = v___y_636_;
v___y_610_ = v___y_635_;
v___y_611_ = v___y_637_;
v_a_612_ = v_a_639_;
goto v___jp_601_;
}
else
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___y_638_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___y_638_, 1);
v___y_615_ = v___y_628_;
v___y_616_ = v___y_629_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_632_;
v___y_619_ = v___y_631_;
v___y_620_ = v___y_634_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_636_;
v___y_623_ = v___y_635_;
v___y_624_ = v___y_637_;
v_a_625_ = v_a_640_;
goto v___jp_614_;
}
}
v___jp_641_:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_651_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_trace_profiler_useHeartbeats;
v___x_658_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_650_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_io_mono_nanos_now();
v___x_660_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_644_, v___y_648_, v___y_651_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_dec_ref_known(v___x_660_, 1);
if (lean_obj_tag(v___y_653_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_val_661_ = lean_ctor_get(v___y_653_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v___y_653_, 1);
v___x_662_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_645_);
v___x_663_ = l_Lean_Name_mkStr2(v___y_645_, v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_663_);
v___x_665_ = l_Lean_Name_append(v___x_664_, v___x_663_);
v___x_666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_643_, v___y_650_, v___x_665_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec(v___x_663_);
lean_dec(v_val_661_);
v___x_667_ = lean_box(0);
v___y_602_ = v___y_648_;
v___y_603_ = v___y_649_;
v___y_604_ = v___y_650_;
v___y_605_ = v___y_652_;
v___y_606_ = v___y_651_;
v___y_607_ = v___x_659_;
v___y_608_ = v___y_646_;
v___y_609_ = v___y_647_;
v___y_610_ = v_a_656_;
v___y_611_ = v___y_654_;
v_a_612_ = v___x_667_;
goto v___jp_601_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_box(0);
v___x_669_ = l_Lean_Elab_InfoTree_format(v_val_661_, v___x_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_MessageData_ofFormat(v_a_670_);
v___x_672_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_663_, v___x_671_, v___y_648_, v___y_651_);
v___y_628_ = v___y_648_;
v___y_629_ = v___y_649_;
v___y_630_ = v___y_650_;
v___y_631_ = v___y_651_;
v___y_632_ = v___y_652_;
v___y_633_ = v___y_646_;
v___y_634_ = v___x_659_;
v___y_635_ = v_a_656_;
v___y_636_ = v___y_647_;
v___y_637_ = v___y_654_;
v___y_638_ = v___x_672_;
goto v___jp_627_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_683_; 
lean_dec(v___x_663_);
v_a_673_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_683_ == 0)
{
v___x_675_ = v___x_669_;
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_io_error_to_string(v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 3);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_682_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Lean_MessageData_ofFormat(v___x_679_);
lean_inc(v___y_642_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_642_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___y_615_ = v___y_648_;
v___y_616_ = v___y_649_;
v___y_617_ = v___y_650_;
v___y_618_ = v___y_652_;
v___y_619_ = v___y_651_;
v___y_620_ = v___x_659_;
v___y_621_ = v___y_646_;
v___y_622_ = v___y_647_;
v___y_623_ = v_a_656_;
v___y_624_ = v___y_654_;
v_a_625_ = v___x_681_;
goto v___jp_614_;
}
}
}
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v___y_653_);
v___x_684_ = lean_box(0);
v___y_602_ = v___y_648_;
v___y_603_ = v___y_649_;
v___y_604_ = v___y_650_;
v___y_605_ = v___y_652_;
v___y_606_ = v___y_651_;
v___y_607_ = v___x_659_;
v___y_608_ = v___y_646_;
v___y_609_ = v___y_647_;
v___y_610_ = v_a_656_;
v___y_611_ = v___y_654_;
v_a_612_ = v___x_684_;
goto v___jp_601_;
}
}
else
{
lean_dec(v___y_653_);
v___y_628_ = v___y_648_;
v___y_629_ = v___y_649_;
v___y_630_ = v___y_650_;
v___y_631_ = v___y_651_;
v___y_632_ = v___y_652_;
v___y_633_ = v___y_646_;
v___y_634_ = v___x_659_;
v___y_635_ = v_a_656_;
v___y_636_ = v___y_647_;
v___y_637_ = v___y_654_;
v___y_638_ = v___x_660_;
goto v___jp_627_;
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_io_get_num_heartbeats();
v___x_686_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_644_, v___y_648_, v___y_651_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref_known(v___x_686_, 1);
if (lean_obj_tag(v___y_653_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_val_687_ = lean_ctor_get(v___y_653_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___y_653_, 1);
v___x_688_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_645_);
v___x_689_ = l_Lean_Name_mkStr2(v___y_645_, v___x_688_);
v___x_690_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_689_);
v___x_691_ = l_Lean_Name_append(v___x_690_, v___x_689_);
v___x_692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_643_, v___y_650_, v___x_691_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec(v___x_689_);
lean_dec(v_val_687_);
v___x_693_ = lean_box(0);
v___y_539_ = v___y_648_;
v___y_540_ = v___y_649_;
v___y_541_ = v___y_650_;
v___y_542_ = v___y_652_;
v___y_543_ = v___y_651_;
v___y_544_ = v___y_646_;
v___y_545_ = v___y_647_;
v___y_546_ = v_a_656_;
v___y_547_ = v___x_685_;
v___y_548_ = v___y_654_;
v_a_549_ = v___x_693_;
goto v___jp_538_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = l_Lean_Elab_InfoTree_format(v_val_687_, v___x_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = l_Lean_MessageData_ofFormat(v_a_696_);
v___x_698_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_689_, v___x_697_, v___y_648_, v___y_651_);
v___y_565_ = v___y_648_;
v___y_566_ = v___y_649_;
v___y_567_ = v___y_650_;
v___y_568_ = v___y_651_;
v___y_569_ = v___y_652_;
v___y_570_ = v___y_646_;
v___y_571_ = v_a_656_;
v___y_572_ = v___y_647_;
v___y_573_ = v___y_654_;
v___y_574_ = v___x_685_;
v___y_575_ = v___x_698_;
goto v___jp_564_;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_709_; 
lean_dec(v___x_689_);
v_a_699_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_709_ == 0)
{
v___x_701_ = v___x_695_;
v_isShared_702_ = v_isSharedCheck_709_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_709_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_io_error_to_string(v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 3);
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_708_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = l_Lean_MessageData_ofFormat(v___x_705_);
lean_inc(v___y_642_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_642_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___y_552_ = v___y_648_;
v___y_553_ = v___y_649_;
v___y_554_ = v___y_650_;
v___y_555_ = v___y_652_;
v___y_556_ = v___y_651_;
v___y_557_ = v___y_646_;
v___y_558_ = v___y_647_;
v___y_559_ = v_a_656_;
v___y_560_ = v___x_685_;
v___y_561_ = v___y_654_;
v_a_562_ = v___x_707_;
goto v___jp_551_;
}
}
}
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v___y_653_);
v___x_710_ = lean_box(0);
v___y_539_ = v___y_648_;
v___y_540_ = v___y_649_;
v___y_541_ = v___y_650_;
v___y_542_ = v___y_652_;
v___y_543_ = v___y_651_;
v___y_544_ = v___y_646_;
v___y_545_ = v___y_647_;
v___y_546_ = v_a_656_;
v___y_547_ = v___x_685_;
v___y_548_ = v___y_654_;
v_a_549_ = v___x_710_;
goto v___jp_538_;
}
}
else
{
lean_dec(v___y_653_);
v___y_565_ = v___y_648_;
v___y_566_ = v___y_649_;
v___y_567_ = v___y_650_;
v___y_568_ = v___y_651_;
v___y_569_ = v___y_652_;
v___y_570_ = v___y_646_;
v___y_571_ = v_a_656_;
v___y_572_ = v___y_647_;
v___y_573_ = v___y_654_;
v___y_574_ = v___x_685_;
v___y_575_ = v___x_686_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v___y_653_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_644_);
v_a_711_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_655_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_655_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
v_resetjp_721_:
{
lean_object* v_desc_724_; lean_object* v_diagnostics_725_; lean_object* v_infoTree_x3f_726_; lean_object* v_desc_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___x_821_; 
v_desc_724_ = lean_ctor_get(v_element_719_, 0);
lean_inc_ref(v_desc_724_);
v_diagnostics_725_ = lean_ctor_get(v_element_719_, 1);
lean_inc_ref(v_diagnostics_725_);
v_infoTree_x3f_726_ = lean_ctor_get(v_element_719_, 2);
lean_inc(v_infoTree_x3f_726_);
lean_dec_ref(v_element_719_);
v___x_821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_821_, 0, v_desc_724_);
switch(lean_obj_tag(v_range_x3f_513_))
{
case 0:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v_desc_728_ = v___x_823_;
v___y_729_ = v_a_515_;
v___y_730_ = v_a_516_;
goto v___jp_727_;
}
case 1:
{
lean_object* v_toCold_824_; lean_object* v_range_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_883_; 
v_toCold_824_ = lean_ctor_get(v_a_515_, 0);
v_range_825_ = lean_ctor_get(v_range_x3f_513_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_range_x3f_513_);
if (v_isSharedCheck_883_ == 0)
{
v___x_827_ = v_range_x3f_513_;
v_isShared_828_ = v_isSharedCheck_883_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_range_825_);
lean_dec(v_range_x3f_513_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_883_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_fileMap_829_; lean_object* v_start_830_; lean_object* v_stop_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_882_; 
v_fileMap_829_ = lean_ctor_get(v_toCold_824_, 1);
v_start_830_ = lean_ctor_get(v_range_825_, 0);
v_stop_831_ = lean_ctor_get(v_range_825_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_range_825_);
if (v_isSharedCheck_882_ == 0)
{
v___x_833_ = v_range_825_;
v_isShared_834_ = v_isSharedCheck_882_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_stop_831_);
lean_inc(v_start_830_);
lean_dec(v_range_825_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_882_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_line_836_; lean_object* v_column_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_881_; 
lean_inc_ref(v_fileMap_829_);
v___x_835_ = l_Lean_FileMap_toPosition(v_fileMap_829_, v_start_830_);
lean_dec(v_start_830_);
v_line_836_ = lean_ctor_get(v___x_835_, 0);
v_column_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_881_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_881_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_column_837_);
lean_inc(v_line_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_881_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v_line_842_; lean_object* v_column_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_880_; 
lean_inc_ref(v_fileMap_829_);
v___x_841_ = l_Lean_FileMap_toPosition(v_fileMap_829_, v_stop_831_);
lean_dec(v_stop_831_);
v_line_842_ = lean_ctor_get(v___x_841_, 0);
v_column_843_ = lean_ctor_get(v___x_841_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_880_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_880_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_column_843_);
lean_inc(v_line_842_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_880_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_848_ = l_Nat_reprFast(v_line_836_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 3);
lean_ctor_set(v___x_827_, 0, v___x_848_);
v___x_850_ = v___x_827_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_879_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 5);
lean_ctor_set(v___x_845_, 1, v___x_850_);
lean_ctor_set(v___x_845_, 0, v___x_847_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_878_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 5);
lean_ctor_set(v___x_839_, 1, v___x_853_);
lean_ctor_set(v___x_839_, 0, v___x_852_);
v___x_855_ = v___x_839_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_877_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = l_Nat_reprFast(v_column_837_);
v___x_857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 5);
lean_ctor_set(v___x_833_, 1, v___x_857_);
lean_ctor_set(v___x_833_, 0, v___x_855_);
v___x_859_ = v___x_833_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_876_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Nat_reprFast(v_line_842_);
v___x_865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_847_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_853_);
v___x_868_ = l_Nat_reprFast(v_column_843_);
v___x_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_867_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_860_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_863_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_821_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v_desc_728_ = v___x_875_;
v___y_729_ = v_a_515_;
v___y_730_ = v_a_516_;
goto v___jp_727_;
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
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_821_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v_desc_728_ = v___x_885_;
v___y_729_ = v_a_515_;
v___y_730_ = v_a_516_;
goto v___jp_727_;
}
}
v___jp_727_:
{
lean_object* v_msgLog_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_819_; 
v_msgLog_731_ = lean_ctor_get(v_diagnostics_725_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_diagnostics_725_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_diagnostics_725_, 1);
lean_dec(v_unused_820_);
v___x_733_ = v_diagnostics_725_;
v_isShared_734_ = v_isSharedCheck_819_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_msgLog_731_);
lean_dec(v_diagnostics_725_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_819_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = l_Lean_MessageLog_toList(v_msgLog_731_);
lean_dec_ref(v_msgLog_731_);
v___x_736_ = lean_box(0);
v___x_737_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_735_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_toCold_738_; lean_object* v_options_739_; lean_object* v_a_740_; lean_object* v_ref_741_; lean_object* v_inheritedTraceOptions_742_; uint8_t v_hasTrace_743_; lean_object* v___x_744_; 
v_toCold_738_ = lean_ctor_get(v___y_729_, 0);
v_options_739_ = lean_ctor_get(v_toCold_738_, 2);
v_a_740_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_737_, 1);
v_ref_741_ = lean_ctor_get(v___y_729_, 2);
v_inheritedTraceOptions_742_ = lean_ctor_get(v_toCold_738_, 11);
v_hasTrace_743_ = lean_ctor_get_uint8(v_options_739_, sizeof(void*)*1);
v___x_744_ = lean_array_to_list(v_children_720_);
if (v_hasTrace_743_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v_a_740_);
lean_del_object(v___x_733_);
lean_dec(v_desc_728_);
lean_dec(v_infoTree_x3f_726_);
lean_del_object(v___x_722_);
v___x_745_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_744_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v___x_745_, 0);
lean_dec(v_unused_754_);
v___x_747_ = v___x_745_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_dec(v___x_745_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_box(0);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
return v___x_745_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_756_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_757_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_756_, v_a_740_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 5);
lean_ctor_set(v___x_733_, 1, v___x_757_);
lean_ctor_set(v___x_733_, 0, v_desc_728_);
v___x_759_ = v___x_733_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_desc_728_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_810_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___f_760_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_760_, 0, v___x_759_);
v___x_761_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_762_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_763_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_742_, v_options_739_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = l_Lean_trace_profiler;
v___x_766_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_739_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v___f_760_);
v___x_767_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_744_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_809_);
v___x_769_ = v___x_767_;
v_isShared_770_ = v_isSharedCheck_808_;
goto v_resetjp_768_;
}
else
{
lean_dec(v___x_767_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_808_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
if (lean_obj_tag(v_infoTree_x3f_726_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_803_; 
v_val_771_ = lean_ctor_get(v_infoTree_x3f_726_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_infoTree_x3f_726_);
if (v_isSharedCheck_803_ == 0)
{
v___x_773_ = v_infoTree_x3f_726_;
v_isShared_774_ = v_isSharedCheck_803_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v_infoTree_x3f_726_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_803_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_776_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_742_, v_options_739_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_del_object(v___x_773_);
lean_dec(v_val_771_);
lean_del_object(v___x_722_);
v___x_778_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_778_);
v___x_780_ = v___x_769_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_del_object(v___x_769_);
v___x_782_ = lean_box(0);
v___x_783_ = l_Lean_Elab_InfoTree_format(v_val_771_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_773_);
lean_del_object(v___x_722_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = l_Lean_MessageData_ofFormat(v_a_784_);
v___x_786_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_775_, v___x_785_, v___y_729_, v___y_730_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_802_; 
v_a_787_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_802_ == 0)
{
v___x_789_ = v___x_783_;
v_isShared_790_ = v_isSharedCheck_802_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_802_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_io_error_to_string(v_a_787_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 3);
lean_ctor_set(v___x_773_, 0, v___x_791_);
v___x_793_ = v___x_773_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_801_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = l_Lean_MessageData_ofFormat(v___x_793_);
lean_inc(v_ref_741_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_794_);
lean_ctor_set(v___x_722_, 0, v_ref_741_);
v___x_796_ = v___x_722_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_ref_741_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_796_);
v___x_798_ = v___x_789_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
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
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v_infoTree_x3f_726_);
lean_del_object(v___x_722_);
v___x_804_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_804_);
v___x_806_ = v___x_769_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_726_);
lean_del_object(v___x_722_);
return v___x_767_;
}
}
else
{
lean_del_object(v___x_722_);
v___y_642_ = v_ref_741_;
v___y_643_ = v_inheritedTraceOptions_742_;
v___y_644_ = v___x_744_;
v___y_645_ = v___x_755_;
v___y_646_ = v___f_760_;
v___y_647_ = v___x_761_;
v___y_648_ = v___y_729_;
v___y_649_ = v_hasTrace_743_;
v___y_650_ = v_options_739_;
v___y_651_ = v___y_730_;
v___y_652_ = v___x_762_;
v___y_653_ = v_infoTree_x3f_726_;
v___y_654_ = v___x_764_;
goto v___jp_641_;
}
}
else
{
lean_del_object(v___x_722_);
v___y_642_ = v_ref_741_;
v___y_643_ = v_inheritedTraceOptions_742_;
v___y_644_ = v___x_744_;
v___y_645_ = v___x_755_;
v___y_646_ = v___f_760_;
v___y_647_ = v___x_761_;
v___y_648_ = v___y_729_;
v___y_649_ = v_hasTrace_743_;
v___y_650_ = v_options_739_;
v___y_651_ = v___y_730_;
v___y_652_ = v___x_762_;
v___y_653_ = v_infoTree_x3f_726_;
v___y_654_ = v___x_764_;
goto v___jp_641_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_del_object(v___x_733_);
lean_dec(v_desc_728_);
lean_dec(v_infoTree_x3f_726_);
lean_del_object(v___x_722_);
lean_dec_ref(v_children_720_);
v_a_811_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_737_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_737_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
if (lean_obj_tag(v_as_887_) == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v_head_893_; lean_object* v_tail_894_; lean_object* v_reportingRange_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_head_893_ = lean_ctor_get(v_as_887_, 0);
lean_inc(v_head_893_);
v_tail_894_ = lean_ctor_get(v_as_887_, 1);
lean_inc(v_tail_894_);
lean_dec_ref_known(v_as_887_, 2);
v_reportingRange_895_ = lean_ctor_get(v_head_893_, 1);
lean_inc(v_reportingRange_895_);
v___x_896_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_893_);
v___x_897_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_895_, v___x_896_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
v_as_887_ = v_tail_894_;
goto _start;
}
else
{
lean_dec(v_tail_894_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_904_, lean_object* v_s_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_904_, v_s_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_910_, v_x_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_916_, v_x_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_928_, v_x_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_box(2);
v___x_939_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_938_, v_s_934_, v_a_935_, v_a_936_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Language_SnapshotTree_trace(v_s_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_944_;
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

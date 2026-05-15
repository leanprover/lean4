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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4;
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
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<no range> "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_12_; lean_object* v_traceState_13_; lean_object* v_traces_14_; lean_object* v___x_15_; lean_object* v_traceState_16_; lean_object* v_env_17_; lean_object* v_nextMacroScope_18_; lean_object* v_ngen_19_; lean_object* v_auxDeclNGen_20_; lean_object* v_cache_21_; lean_object* v_messages_22_; lean_object* v_infoState_23_; lean_object* v_snapshotTasks_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_43_; 
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
v_messages_22_ = lean_ctor_get(v___x_15_, 6);
v_infoState_23_ = lean_ctor_get(v___x_15_, 7);
v_snapshotTasks_24_ = lean_ctor_get(v___x_15_, 8);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_43_ == 0)
{
v___x_26_ = v___x_15_;
v_isShared_27_ = v_isSharedCheck_43_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_snapshotTasks_24_);
lean_inc(v_infoState_23_);
lean_inc(v_messages_22_);
lean_inc(v_cache_21_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_20_);
lean_inc(v_ngen_19_);
lean_inc(v_nextMacroScope_18_);
lean_inc(v_env_17_);
lean_dec(v___x_15_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_43_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
uint64_t v_tid_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_41_; 
v_tid_28_ = lean_ctor_get_uint64(v_traceState_16_, sizeof(void*)*1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_traceState_16_);
if (v_isSharedCheck_41_ == 0)
{
lean_object* v_unused_42_; 
v_unused_42_ = lean_ctor_get(v_traceState_16_, 0);
lean_dec(v_unused_42_);
v___x_30_ = v_traceState_16_;
v_isShared_31_ = v_isSharedCheck_41_;
goto v_resetjp_29_;
}
else
{
lean_dec(v_traceState_16_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_41_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___closed__1);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_32_);
lean_ctor_set_uint64(v_reuseFailAlloc_40_, sizeof(void*)*1, v_tid_28_);
v___x_34_ = v_reuseFailAlloc_40_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_36_; 
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 4, v___x_34_);
v___x_36_ = v___x_26_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_env_17_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_nextMacroScope_18_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v_ngen_19_);
lean_ctor_set(v_reuseFailAlloc_39_, 3, v_auxDeclNGen_20_);
lean_ctor_set(v_reuseFailAlloc_39_, 4, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_39_, 5, v_cache_21_);
lean_ctor_set(v_reuseFailAlloc_39_, 6, v_messages_22_);
lean_ctor_set(v_reuseFailAlloc_39_, 7, v_infoState_23_);
lean_ctor_set(v_reuseFailAlloc_39_, 8, v_snapshotTasks_24_);
v___x_36_ = v_reuseFailAlloc_39_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_st_ref_set(v___y_10_, v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v_traces_14_);
return v___x_38_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg___boxed(lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_44_);
lean_dec(v___y_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object* v_opts_55_, lean_object* v_opt_56_){
_start:
{
lean_object* v_name_57_; lean_object* v_defValue_58_; lean_object* v_map_59_; lean_object* v___x_60_; 
v_name_57_ = lean_ctor_get(v_opt_56_, 0);
v_defValue_58_ = lean_ctor_get(v_opt_56_, 1);
v_map_59_ = lean_ctor_get(v_opts_55_, 0);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_59_, v_name_57_);
if (lean_obj_tag(v___x_60_) == 0)
{
uint8_t v___x_61_; 
v___x_61_ = lean_unbox(v_defValue_58_);
return v___x_61_;
}
else
{
lean_object* v_val_62_; 
v_val_62_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_val_62_);
lean_dec_ref(v___x_60_);
if (lean_obj_tag(v_val_62_) == 1)
{
uint8_t v_v_63_; 
v_v_63_ = lean_ctor_get_uint8(v_val_62_, 0);
lean_dec_ref(v_val_62_);
return v_v_63_;
}
else
{
uint8_t v___x_64_; 
lean_dec(v_val_62_);
v___x_64_ = lean_unbox(v_defValue_58_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object* v_opts_65_, lean_object* v_opt_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_65_, v_opt_66_);
lean_dec_ref(v_opt_66_);
lean_dec_ref(v_opts_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object* v___x_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = l_Lean_MessageData_ofFormat(v___x_69_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object* v___x_76_, lean_object* v_x_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(v___x_76_, v_x_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec_ref(v_x_77_);
return v_res_81_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_82_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__0);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
lean_ctor_set(v___x_87_, 3, v___x_86_);
lean_ctor_set(v___x_87_, 4, v___x_85_);
lean_ctor_set(v___x_87_, 5, v___x_85_);
lean_ctor_set(v___x_87_, 6, v___x_85_);
lean_ctor_set(v___x_87_, 7, v___x_85_);
lean_ctor_set(v___x_87_, 8, v___x_85_);
lean_ctor_set(v___x_87_, 9, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_unsigned_to_nat(32u);
v___x_89_ = lean_mk_empty_array_with_capacity(v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_91_ = ((size_t)5ULL);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_unsigned_to_nat(32u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
v___x_96_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_92_);
lean_ctor_set(v___x_96_, 3, v___x_92_);
lean_ctor_set_usize(v___x_96_, 4, v___x_91_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_box(1);
v___x_98_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_env_106_; lean_object* v_options_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v_options_107_ = lean_ctor_get(v___y_102_, 2);
v___x_108_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_107_);
v___x_110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_110_, 0, v_env_106_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_109_);
lean_ctor_set(v___x_110_, 3, v_options_107_);
v___x_111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_msgData_101_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_117_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_118_; double v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_float_of_nat(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_ref_128_; lean_object* v___x_129_; lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_174_; 
v_ref_128_ = lean_ctor_get(v___y_125_, 5);
v___x_129_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_124_, v___y_125_, v___y_126_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_174_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_174_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_174_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v_traceState_135_; lean_object* v_env_136_; lean_object* v_nextMacroScope_137_; lean_object* v_ngen_138_; lean_object* v_auxDeclNGen_139_; lean_object* v_cache_140_; lean_object* v_messages_141_; lean_object* v_infoState_142_; lean_object* v_snapshotTasks_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_173_; 
v___x_134_ = lean_st_ref_take(v___y_126_);
v_traceState_135_ = lean_ctor_get(v___x_134_, 4);
v_env_136_ = lean_ctor_get(v___x_134_, 0);
v_nextMacroScope_137_ = lean_ctor_get(v___x_134_, 1);
v_ngen_138_ = lean_ctor_get(v___x_134_, 2);
v_auxDeclNGen_139_ = lean_ctor_get(v___x_134_, 3);
v_cache_140_ = lean_ctor_get(v___x_134_, 5);
v_messages_141_ = lean_ctor_get(v___x_134_, 6);
v_infoState_142_ = lean_ctor_get(v___x_134_, 7);
v_snapshotTasks_143_ = lean_ctor_get(v___x_134_, 8);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_173_ == 0)
{
v___x_145_ = v___x_134_;
v_isShared_146_ = v_isSharedCheck_173_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_snapshotTasks_143_);
lean_inc(v_infoState_142_);
lean_inc(v_messages_141_);
lean_inc(v_cache_140_);
lean_inc(v_traceState_135_);
lean_inc(v_auxDeclNGen_139_);
lean_inc(v_ngen_138_);
lean_inc(v_nextMacroScope_137_);
lean_inc(v_env_136_);
lean_dec(v___x_134_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_173_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
uint64_t v_tid_147_; lean_object* v_traces_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_172_; 
v_tid_147_ = lean_ctor_get_uint64(v_traceState_135_, sizeof(void*)*1);
v_traces_148_ = lean_ctor_get(v_traceState_135_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_traceState_135_);
if (v_isSharedCheck_172_ == 0)
{
v___x_150_ = v_traceState_135_;
v_isShared_151_ = v_isSharedCheck_172_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_traces_148_);
lean_dec(v_traceState_135_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_172_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; double v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_152_ = lean_box(0);
v___x_153_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_154_ = 0;
v___x_155_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_156_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_156_, 0, v_cls_123_);
lean_ctor_set(v___x_156_, 1, v___x_152_);
lean_ctor_set(v___x_156_, 2, v___x_155_);
lean_ctor_set_float(v___x_156_, sizeof(void*)*3, v___x_153_);
lean_ctor_set_float(v___x_156_, sizeof(void*)*3 + 8, v___x_153_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*3 + 16, v___x_154_);
v___x_157_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_158_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v_a_130_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_inc(v_ref_128_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v_ref_128_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_PersistentArray_push___redArg(v_traces_148_, v___x_159_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_160_);
v___x_162_ = v___x_150_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_160_);
lean_ctor_set_uint64(v_reuseFailAlloc_171_, sizeof(void*)*1, v_tid_147_);
v___x_162_ = v_reuseFailAlloc_171_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_162_);
v___x_164_ = v___x_145_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_env_136_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_nextMacroScope_137_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_ngen_138_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_auxDeclNGen_139_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_170_, 5, v_cache_140_);
lean_ctor_set(v_reuseFailAlloc_170_, 6, v_messages_141_);
lean_ctor_set(v_reuseFailAlloc_170_, 7, v_infoState_142_);
lean_ctor_set(v_reuseFailAlloc_170_, 8, v_snapshotTasks_143_);
v___x_164_ = v_reuseFailAlloc_170_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_165_ = lean_st_ref_set(v___y_126_, v___x_164_);
v___x_166_ = lean_box(0);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_166_);
v___x_168_ = v___x_132_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_175_, lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_175_, v_msg_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_dec(v_pre_181_);
return v_x_182_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_195_; 
v_head_184_ = lean_ctor_get(v_x_183_, 0);
v_tail_185_ = lean_ctor_get(v_x_183_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_195_ == 0)
{
v___x_187_ = v_x_183_;
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_tail_185_);
lean_inc(v_head_184_);
lean_dec(v_x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
lean_inc(v_pre_181_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 5);
lean_ctor_set(v___x_187_, 1, v_pre_181_);
lean_ctor_set(v___x_187_, 0, v_x_182_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_x_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_pre_181_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_191_, 0, v_head_184_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v_x_182_ = v___x_192_;
v_x_183_ = v_tail_185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_198_; 
lean_dec(v_pre_196_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_head_199_; lean_object* v_tail_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_209_; 
v_head_199_ = lean_ctor_get(v_x_197_, 0);
v_tail_200_ = lean_ctor_get(v_x_197_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_209_ == 0)
{
v___x_202_ = v_x_197_;
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_tail_200_);
lean_inc(v_head_199_);
lean_dec(v_x_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_204_, 0, v_head_199_);
lean_inc(v_pre_196_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 5);
lean_ctor_set(v___x_202_, 1, v___x_204_);
lean_ctor_set(v___x_202_, 0, v_pre_196_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_pre_196_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_196_, v___x_206_, v_tail_200_);
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = l_List_reverse___redArg(v_x_211_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_head_215_; lean_object* v_tail_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_226_; 
v_head_215_ = lean_ctor_get(v_x_210_, 0);
v_tail_216_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_218_ = v_x_210_;
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_tail_216_);
lean_inc(v_head_215_);
lean_dec(v_x_210_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_220_ = 0;
v___x_221_ = l_Lean_Message_toString(v_head_215_, v___x_220_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v_x_211_);
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_x_211_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v_x_210_ = v_tail_216_;
v_x_211_ = v___x_223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_227_, v_x_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(size_t v_sz_231_, size_t v_i_232_, lean_object* v_bs_233_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_bs_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_boxed_246_, v_i_boxed_247_, v_bs_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_oldTraces_249_, lean_object* v_data_250_, lean_object* v_ref_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_fileName_256_; lean_object* v_fileMap_257_; lean_object* v_options_258_; lean_object* v_currRecDepth_259_; lean_object* v_maxRecDepth_260_; lean_object* v_ref_261_; lean_object* v_currNamespace_262_; lean_object* v_openDecls_263_; lean_object* v_initHeartbeats_264_; lean_object* v_maxHeartbeats_265_; lean_object* v_quotContext_266_; lean_object* v_currMacroScope_267_; uint8_t v_diag_268_; lean_object* v_cancelTk_x3f_269_; uint8_t v_suppressElabErrors_270_; lean_object* v_inheritedTraceOptions_271_; lean_object* v___x_272_; lean_object* v_traceState_273_; lean_object* v_traces_274_; lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v_msg_281_; lean_object* v___x_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_320_; 
v_fileName_256_ = lean_ctor_get(v___y_253_, 0);
v_fileMap_257_ = lean_ctor_get(v___y_253_, 1);
v_options_258_ = lean_ctor_get(v___y_253_, 2);
v_currRecDepth_259_ = lean_ctor_get(v___y_253_, 3);
v_maxRecDepth_260_ = lean_ctor_get(v___y_253_, 4);
v_ref_261_ = lean_ctor_get(v___y_253_, 5);
v_currNamespace_262_ = lean_ctor_get(v___y_253_, 6);
v_openDecls_263_ = lean_ctor_get(v___y_253_, 7);
v_initHeartbeats_264_ = lean_ctor_get(v___y_253_, 8);
v_maxHeartbeats_265_ = lean_ctor_get(v___y_253_, 9);
v_quotContext_266_ = lean_ctor_get(v___y_253_, 10);
v_currMacroScope_267_ = lean_ctor_get(v___y_253_, 11);
v_diag_268_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*14);
v_cancelTk_x3f_269_ = lean_ctor_get(v___y_253_, 12);
v_suppressElabErrors_270_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_271_ = lean_ctor_get(v___y_253_, 13);
v___x_272_ = lean_st_ref_get(v___y_254_);
v_traceState_273_ = lean_ctor_get(v___x_272_, 4);
lean_inc_ref(v_traceState_273_);
lean_dec(v___x_272_);
v_traces_274_ = lean_ctor_get(v_traceState_273_, 0);
lean_inc_ref(v_traces_274_);
lean_dec_ref(v_traceState_273_);
v_ref_275_ = l_Lean_replaceRef(v_ref_251_, v_ref_261_);
lean_inc_ref(v_inheritedTraceOptions_271_);
lean_inc(v_cancelTk_x3f_269_);
lean_inc(v_currMacroScope_267_);
lean_inc(v_quotContext_266_);
lean_inc(v_maxHeartbeats_265_);
lean_inc(v_initHeartbeats_264_);
lean_inc(v_openDecls_263_);
lean_inc(v_currNamespace_262_);
lean_inc(v_maxRecDepth_260_);
lean_inc(v_currRecDepth_259_);
lean_inc_ref(v_options_258_);
lean_inc_ref(v_fileMap_257_);
lean_inc_ref(v_fileName_256_);
v___x_276_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_276_, 0, v_fileName_256_);
lean_ctor_set(v___x_276_, 1, v_fileMap_257_);
lean_ctor_set(v___x_276_, 2, v_options_258_);
lean_ctor_set(v___x_276_, 3, v_currRecDepth_259_);
lean_ctor_set(v___x_276_, 4, v_maxRecDepth_260_);
lean_ctor_set(v___x_276_, 5, v_ref_275_);
lean_ctor_set(v___x_276_, 6, v_currNamespace_262_);
lean_ctor_set(v___x_276_, 7, v_openDecls_263_);
lean_ctor_set(v___x_276_, 8, v_initHeartbeats_264_);
lean_ctor_set(v___x_276_, 9, v_maxHeartbeats_265_);
lean_ctor_set(v___x_276_, 10, v_quotContext_266_);
lean_ctor_set(v___x_276_, 11, v_currMacroScope_267_);
lean_ctor_set(v___x_276_, 12, v_cancelTk_x3f_269_);
lean_ctor_set(v___x_276_, 13, v_inheritedTraceOptions_271_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*14, v_diag_268_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*14 + 1, v_suppressElabErrors_270_);
v___x_277_ = l_Lean_PersistentArray_toArray___redArg(v_traces_274_);
lean_dec_ref(v_traces_274_);
v_sz_278_ = lean_array_size(v___x_277_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_278_, v___x_279_, v___x_277_);
v_msg_281_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_281_, 0, v_data_250_);
lean_ctor_set(v_msg_281_, 1, v_msg_252_);
lean_ctor_set(v_msg_281_, 2, v___x_280_);
v___x_282_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_281_, v___x_276_, v___y_254_);
lean_dec_ref(v___x_276_);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_320_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v_traceState_288_; lean_object* v_env_289_; lean_object* v_nextMacroScope_290_; lean_object* v_ngen_291_; lean_object* v_auxDeclNGen_292_; lean_object* v_cache_293_; lean_object* v_messages_294_; lean_object* v_infoState_295_; lean_object* v_snapshotTasks_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_319_; 
v___x_287_ = lean_st_ref_take(v___y_254_);
v_traceState_288_ = lean_ctor_get(v___x_287_, 4);
v_env_289_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_290_ = lean_ctor_get(v___x_287_, 1);
v_ngen_291_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_292_ = lean_ctor_get(v___x_287_, 3);
v_cache_293_ = lean_ctor_get(v___x_287_, 5);
v_messages_294_ = lean_ctor_get(v___x_287_, 6);
v_infoState_295_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_296_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_319_ == 0)
{
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snapshotTasks_296_);
lean_inc(v_infoState_295_);
lean_inc(v_messages_294_);
lean_inc(v_cache_293_);
lean_inc(v_traceState_288_);
lean_inc(v_auxDeclNGen_292_);
lean_inc(v_ngen_291_);
lean_inc(v_nextMacroScope_290_);
lean_inc(v_env_289_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint64_t v_tid_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_317_; 
v_tid_300_ = lean_ctor_get_uint64(v_traceState_288_, sizeof(void*)*1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_traceState_288_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_traceState_288_, 0);
lean_dec(v_unused_318_);
v___x_302_ = v_traceState_288_;
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_traceState_288_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_ref_251_);
lean_ctor_set(v___x_304_, 1, v_a_283_);
v___x_305_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_249_, v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_305_);
lean_ctor_set_uint64(v_reuseFailAlloc_316_, sizeof(void*)*1, v_tid_300_);
v___x_307_ = v_reuseFailAlloc_316_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v___x_307_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_env_289_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_nextMacroScope_290_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_ngen_291_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_auxDeclNGen_292_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v_cache_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_messages_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 7, v_infoState_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 8, v_snapshotTasks_296_);
v___x_309_ = v_reuseFailAlloc_315_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = lean_st_ref_set(v___y_254_, v___x_309_);
v___x_311_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_311_);
v___x_313_ = v___x_285_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_oldTraces_321_, lean_object* v_data_322_, lean_object* v_ref_323_, lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_321_, v_data_322_, v_ref_323_, v_msg_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_329_, lean_object* v_opt_330_){
_start:
{
lean_object* v_name_331_; lean_object* v_defValue_332_; lean_object* v_map_333_; lean_object* v___x_334_; 
v_name_331_ = lean_ctor_get(v_opt_330_, 0);
v_defValue_332_ = lean_ctor_get(v_opt_330_, 1);
v_map_333_ = lean_ctor_get(v_opts_329_, 0);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_333_, v_name_331_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_inc(v_defValue_332_);
return v_defValue_332_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref(v___x_334_);
if (lean_obj_tag(v_val_335_) == 3)
{
lean_object* v_v_336_; 
v_v_336_ = lean_ctor_get(v_val_335_, 0);
lean_inc(v_v_336_);
lean_dec_ref(v_val_335_);
return v_v_336_;
}
else
{
lean_dec(v_val_335_);
lean_inc(v_defValue_332_);
return v_defValue_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_337_, lean_object* v_opt_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_337_, v_opt_338_);
lean_dec_ref(v_opt_338_);
lean_dec_ref(v_opts_337_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_e_340_){
_start:
{
if (lean_obj_tag(v_e_340_) == 0)
{
uint8_t v___x_341_; 
v___x_341_ = 2;
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = 0;
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_e_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_e_343_);
lean_dec_ref(v_e_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_a_348_ = lean_ctor_get(v_x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v_x_346_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v_x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v_x_346_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v_x_346_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v_x_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 0);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg___boxed(lean_object* v_x_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_364_);
return v_res_366_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4(void){
_start:
{
lean_object* v___x_373_; double v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(1000u);
v___x_374_ = lean_float_of_nat(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_375_, uint8_t v_collapsed_376_, lean_object* v_tag_377_, lean_object* v_opts_378_, uint8_t v_clsEnabled_379_, lean_object* v_oldTraces_380_, lean_object* v_msg_381_, lean_object* v_resStartStop_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_477_; 
v_fst_386_ = lean_ctor_get(v_resStartStop_382_, 0);
v_snd_387_ = lean_ctor_get(v_resStartStop_382_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_resStartStop_382_);
if (v_isSharedCheck_477_ == 0)
{
v___x_389_ = v_resStartStop_382_;
v_isShared_390_ = v_isSharedCheck_477_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_inc(v_fst_386_);
lean_dec(v_resStartStop_382_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_477_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v_data_394_; lean_object* v_fst_397_; lean_object* v_snd_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_476_; 
v_fst_397_ = lean_ctor_get(v_snd_387_, 0);
v_snd_398_ = lean_ctor_get(v_snd_387_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_snd_387_);
if (v_isSharedCheck_476_ == 0)
{
v___x_400_ = v_snd_387_;
v_isShared_401_ = v_isSharedCheck_476_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snd_398_);
lean_inc(v_fst_397_);
lean_dec(v_snd_387_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_476_;
goto v_resetjp_399_;
}
v___jp_391_:
{
lean_object* v___x_395_; 
lean_inc(v___y_392_);
v___x_395_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_380_, v_data_394_, v___y_392_, v___y_393_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_395_);
v___x_396_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_386_);
return v___x_396_;
}
else
{
lean_dec(v_fst_386_);
return v___x_395_;
}
}
v_resetjp_399_:
{
lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___y_405_; lean_object* v_a_406_; uint8_t v___y_430_; double v___y_461_; 
v___x_402_ = l_Lean_trace_profiler;
v___x_403_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_378_, v___x_402_);
if (v___x_403_ == 0)
{
v___y_430_ = v___x_403_;
goto v___jp_429_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = l_Lean_trace_profiler_useHeartbeats;
v___x_467_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_378_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; double v___x_470_; double v___x_471_; double v___x_472_; 
v___x_468_ = l_Lean_trace_profiler_threshold;
v___x_469_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_378_, v___x_468_);
v___x_470_ = lean_float_of_nat(v___x_469_);
v___x_471_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4);
v___x_472_ = lean_float_div(v___x_470_, v___x_471_);
v___y_461_ = v___x_472_;
goto v___jp_460_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; double v___x_475_; 
v___x_473_ = l_Lean_trace_profiler_threshold;
v___x_474_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_378_, v___x_473_);
v___x_475_ = lean_float_of_nat(v___x_474_);
v___y_461_ = v___x_475_;
goto v___jp_460_;
}
}
v___jp_404_:
{
uint8_t v_result_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v_result_407_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_fst_386_);
v___x_408_ = l_Lean_TraceResult_toEmoji(v_result_407_);
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
v___x_410_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 7);
lean_ctor_set(v___x_400_, 1, v___x_410_);
lean_ctor_set(v___x_400_, 0, v___x_409_);
v___x_412_ = v___x_400_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_423_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v_m_414_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 7);
lean_ctor_set(v___x_389_, 1, v_a_406_);
lean_ctor_set(v___x_389_, 0, v___x_412_);
v_m_414_ = v___x_389_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_a_406_);
v_m_414_ = v_reuseFailAlloc_422_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; double v___x_417_; lean_object* v_data_418_; 
v___x_415_ = lean_box(v_result_407_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_377_);
lean_inc_ref(v___x_416_);
lean_inc(v_cls_375_);
v_data_418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_418_, 0, v_cls_375_);
lean_ctor_set(v_data_418_, 1, v___x_416_);
lean_ctor_set(v_data_418_, 2, v_tag_377_);
lean_ctor_set_float(v_data_418_, sizeof(void*)*3, v___x_417_);
lean_ctor_set_float(v_data_418_, sizeof(void*)*3 + 8, v___x_417_);
lean_ctor_set_uint8(v_data_418_, sizeof(void*)*3 + 16, v_collapsed_376_);
if (v___x_403_ == 0)
{
lean_dec_ref(v___x_416_);
lean_dec(v_snd_398_);
lean_dec(v_fst_397_);
lean_dec_ref(v_tag_377_);
lean_dec(v_cls_375_);
v___y_392_ = v___y_405_;
v___y_393_ = v_m_414_;
v_data_394_ = v_data_418_;
goto v___jp_391_;
}
else
{
lean_object* v_data_419_; double v___x_420_; double v___x_421_; 
lean_dec_ref(v_data_418_);
v_data_419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_419_, 0, v_cls_375_);
lean_ctor_set(v_data_419_, 1, v___x_416_);
lean_ctor_set(v_data_419_, 2, v_tag_377_);
v___x_420_ = lean_unbox_float(v_fst_397_);
lean_dec(v_fst_397_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3, v___x_420_);
v___x_421_ = lean_unbox_float(v_snd_398_);
lean_dec(v_snd_398_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3 + 8, v___x_421_);
lean_ctor_set_uint8(v_data_419_, sizeof(void*)*3 + 16, v_collapsed_376_);
v___y_392_ = v___y_405_;
v___y_393_ = v_m_414_;
v_data_394_ = v_data_419_;
goto v___jp_391_;
}
}
}
}
v___jp_424_:
{
lean_object* v_ref_425_; lean_object* v___x_426_; 
v_ref_425_ = lean_ctor_get(v___y_383_, 5);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v_fst_386_);
v___x_426_ = lean_apply_4(v_msg_381_, v_fst_386_, v___y_383_, v___y_384_, lean_box(0));
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
v___y_405_ = v_ref_425_;
v_a_406_ = v_a_427_;
goto v___jp_404_;
}
else
{
lean_object* v___x_428_; 
lean_dec_ref(v___x_426_);
v___x_428_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3);
v___y_405_ = v_ref_425_;
v_a_406_ = v___x_428_;
goto v___jp_404_;
}
}
v___jp_429_:
{
if (v_clsEnabled_379_ == 0)
{
if (v___y_430_ == 0)
{
lean_object* v___x_431_; lean_object* v_traceState_432_; lean_object* v_env_433_; lean_object* v_nextMacroScope_434_; lean_object* v_ngen_435_; lean_object* v_auxDeclNGen_436_; lean_object* v_cache_437_; lean_object* v_messages_438_; lean_object* v_infoState_439_; lean_object* v_snapshotTasks_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_459_; 
lean_del_object(v___x_400_);
lean_dec(v_snd_398_);
lean_dec(v_fst_397_);
lean_del_object(v___x_389_);
lean_dec_ref(v_msg_381_);
lean_dec_ref(v_tag_377_);
lean_dec(v_cls_375_);
v___x_431_ = lean_st_ref_take(v___y_384_);
v_traceState_432_ = lean_ctor_get(v___x_431_, 4);
v_env_433_ = lean_ctor_get(v___x_431_, 0);
v_nextMacroScope_434_ = lean_ctor_get(v___x_431_, 1);
v_ngen_435_ = lean_ctor_get(v___x_431_, 2);
v_auxDeclNGen_436_ = lean_ctor_get(v___x_431_, 3);
v_cache_437_ = lean_ctor_get(v___x_431_, 5);
v_messages_438_ = lean_ctor_get(v___x_431_, 6);
v_infoState_439_ = lean_ctor_get(v___x_431_, 7);
v_snapshotTasks_440_ = lean_ctor_get(v___x_431_, 8);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_459_ == 0)
{
v___x_442_ = v___x_431_;
v_isShared_443_ = v_isSharedCheck_459_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snapshotTasks_440_);
lean_inc(v_infoState_439_);
lean_inc(v_messages_438_);
lean_inc(v_cache_437_);
lean_inc(v_traceState_432_);
lean_inc(v_auxDeclNGen_436_);
lean_inc(v_ngen_435_);
lean_inc(v_nextMacroScope_434_);
lean_inc(v_env_433_);
lean_dec(v___x_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_459_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint64_t v_tid_444_; lean_object* v_traces_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_458_; 
v_tid_444_ = lean_ctor_get_uint64(v_traceState_432_, sizeof(void*)*1);
v_traces_445_ = lean_ctor_get(v_traceState_432_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_traceState_432_);
if (v_isSharedCheck_458_ == 0)
{
v___x_447_ = v_traceState_432_;
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_traces_445_);
lean_dec(v_traceState_432_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_380_, v_traces_445_);
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
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_env_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_nextMacroScope_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_ngen_435_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_auxDeclNGen_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_cache_437_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_messages_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_infoState_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_snapshotTasks_440_);
v___x_453_ = v_reuseFailAlloc_456_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_st_ref_set(v___y_384_, v___x_453_);
v___x_455_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_386_);
return v___x_455_;
}
}
}
}
}
else
{
goto v___jp_424_;
}
}
else
{
goto v___jp_424_;
}
}
v___jp_460_:
{
double v___x_462_; double v___x_463_; double v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unbox_float(v_snd_398_);
v___x_463_ = lean_unbox_float(v_fst_397_);
v___x_464_ = lean_float_sub(v___x_462_, v___x_463_);
v___x_465_ = lean_float_decLt(v___y_461_, v___x_464_);
v___y_430_ = v___x_465_;
goto v___jp_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_478_, lean_object* v_collapsed_479_, lean_object* v_tag_480_, lean_object* v_opts_481_, lean_object* v_clsEnabled_482_, lean_object* v_oldTraces_483_, lean_object* v_msg_484_, lean_object* v_resStartStop_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_collapsed_boxed_489_; uint8_t v_clsEnabled_boxed_490_; lean_object* v_res_491_; 
v_collapsed_boxed_489_ = lean_unbox(v_collapsed_479_);
v_clsEnabled_boxed_490_ = lean_unbox(v_clsEnabled_482_);
v_res_491_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_478_, v_collapsed_boxed_489_, v_tag_480_, v_opts_481_, v_clsEnabled_boxed_490_, v_oldTraces_483_, v_msg_484_, v_resStartStop_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_opts_481_);
return v_res_491_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_492_; double v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(1000000000u);
v___x_493_ = lean_float_of_nat(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_507_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_508_ = l_Lean_Name_append(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_513_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_514_ = l_Lean_Name_append(v___x_513_, v___x_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_535_, lean_object* v_s_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v_a_551_; lean_object* v___y_561_; uint8_t v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v_a_571_; lean_object* v___y_574_; uint8_t v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v_a_584_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; uint8_t v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_a_611_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; uint8_t v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v_a_634_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v_a_647_; lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v_element_741_; lean_object* v_children_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_910_; 
v_element_741_ = lean_ctor_get(v_s_536_, 0);
v_children_742_ = lean_ctor_get(v_s_536_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_s_536_);
if (v_isSharedCheck_910_ == 0)
{
v___x_744_ = v_s_536_;
v_isShared_745_ = v_isSharedCheck_910_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_children_742_);
lean_inc(v_element_741_);
lean_dec(v_s_536_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_910_;
goto v_resetjp_743_;
}
v___jp_540_:
{
lean_object* v___x_552_; double v___x_553_; double v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_552_ = lean_io_get_num_heartbeats();
v___x_553_ = lean_float_of_nat(v___y_548_);
v___x_554_ = lean_float_of_nat(v___x_552_);
v___x_555_ = lean_box_float(v___x_553_);
v___x_556_ = lean_box_float(v___x_554_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_a_551_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_inc_ref(v___y_546_);
lean_inc(v___y_547_);
v___x_559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_547_, v___y_544_, v___y_546_, v___y_549_, v___y_542_, v___y_545_, v___y_541_, v___x_558_, v___y_550_, v___y_543_);
return v___x_559_;
}
v___jp_560_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_a_571_);
v___y_541_ = v___y_561_;
v___y_542_ = v___y_562_;
v___y_543_ = v___y_564_;
v___y_544_ = v___y_563_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_566_;
v___y_547_ = v___y_565_;
v___y_548_ = v___y_568_;
v___y_549_ = v___y_569_;
v___y_550_ = v___y_570_;
v_a_551_ = v___x_572_;
goto v___jp_540_;
}
v___jp_573_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v_a_584_);
v___y_541_ = v___y_574_;
v___y_542_ = v___y_575_;
v___y_543_ = v___y_577_;
v___y_544_ = v___y_576_;
v___y_545_ = v___y_580_;
v___y_546_ = v___y_579_;
v___y_547_ = v___y_578_;
v___y_548_ = v___y_581_;
v___y_549_ = v___y_582_;
v___y_550_ = v___y_583_;
v_a_551_ = v___x_585_;
goto v___jp_540_;
}
v___jp_586_:
{
if (lean_obj_tag(v___y_597_) == 0)
{
lean_object* v_a_598_; 
v_a_598_ = lean_ctor_get(v___y_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___y_597_);
v___y_561_ = v___y_587_;
v___y_562_ = v___y_588_;
v___y_563_ = v___y_590_;
v___y_564_ = v___y_589_;
v___y_565_ = v___y_593_;
v___y_566_ = v___y_592_;
v___y_567_ = v___y_591_;
v___y_568_ = v___y_594_;
v___y_569_ = v___y_595_;
v___y_570_ = v___y_596_;
v_a_571_ = v_a_598_;
goto v___jp_560_;
}
else
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___y_597_, 0);
lean_inc(v_a_599_);
lean_dec_ref(v___y_597_);
v___y_574_ = v___y_587_;
v___y_575_ = v___y_588_;
v___y_576_ = v___y_590_;
v___y_577_ = v___y_589_;
v___y_578_ = v___y_593_;
v___y_579_ = v___y_592_;
v___y_580_ = v___y_591_;
v___y_581_ = v___y_594_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v_a_584_ = v_a_599_;
goto v___jp_573_;
}
}
v___jp_600_:
{
lean_object* v___x_612_; double v___x_613_; double v___x_614_; double v___x_615_; double v___x_616_; double v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_612_ = lean_io_mono_nanos_now();
v___x_613_ = lean_float_of_nat(v___y_602_);
v___x_614_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_615_ = lean_float_div(v___x_613_, v___x_614_);
v___x_616_ = lean_float_of_nat(v___x_612_);
v___x_617_ = lean_float_div(v___x_616_, v___x_614_);
v___x_618_ = lean_box_float(v___x_615_);
v___x_619_ = lean_box_float(v___x_617_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_a_611_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_608_);
v___x_622_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_608_, v___y_605_, v___y_607_, v___y_609_, v___y_603_, v___y_606_, v___y_601_, v___x_621_, v___y_610_, v___y_604_);
return v___x_622_;
}
v___jp_623_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v_a_634_);
v___y_601_ = v___y_624_;
v___y_602_ = v___y_625_;
v___y_603_ = v___y_626_;
v___y_604_ = v___y_628_;
v___y_605_ = v___y_627_;
v___y_606_ = v___y_631_;
v___y_607_ = v___y_630_;
v___y_608_ = v___y_629_;
v___y_609_ = v___y_632_;
v___y_610_ = v___y_633_;
v_a_611_ = v___x_635_;
goto v___jp_600_;
}
v___jp_636_:
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v_a_647_);
v___y_601_ = v___y_637_;
v___y_602_ = v___y_638_;
v___y_603_ = v___y_639_;
v___y_604_ = v___y_641_;
v___y_605_ = v___y_640_;
v___y_606_ = v___y_644_;
v___y_607_ = v___y_643_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_645_;
v___y_610_ = v___y_646_;
v_a_611_ = v___x_648_;
goto v___jp_600_;
}
v___jp_649_:
{
if (lean_obj_tag(v___y_660_) == 0)
{
lean_object* v_a_661_; 
v_a_661_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___y_660_);
v___y_624_ = v___y_650_;
v___y_625_ = v___y_651_;
v___y_626_ = v___y_652_;
v___y_627_ = v___y_654_;
v___y_628_ = v___y_653_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_656_;
v___y_631_ = v___y_655_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_659_;
v_a_634_ = v_a_661_;
goto v___jp_623_;
}
else
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v___y_660_);
v___y_637_ = v___y_650_;
v___y_638_ = v___y_651_;
v___y_639_ = v___y_652_;
v___y_640_ = v___y_654_;
v___y_641_ = v___y_653_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_656_;
v___y_644_ = v___y_655_;
v___y_645_ = v___y_658_;
v___y_646_ = v___y_659_;
v_a_647_ = v_a_662_;
goto v___jp_636_;
}
}
v___jp_663_:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_670_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
v___x_679_ = l_Lean_trace_profiler_useHeartbeats;
v___x_680_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_667_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_io_mono_nanos_now();
v___x_682_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_675_, v___y_668_, v___y_670_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_dec_ref(v___x_682_);
if (lean_obj_tag(v___y_676_) == 1)
{
lean_object* v_val_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_val_683_ = lean_ctor_get(v___y_676_, 0);
lean_inc(v_val_683_);
lean_dec_ref(v___y_676_);
v___x_684_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_666_);
v___x_685_ = l_Lean_Name_mkStr2(v___y_666_, v___x_684_);
v___x_686_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_685_);
v___x_687_ = l_Lean_Name_append(v___x_686_, v___x_685_);
v___x_688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_674_, v___y_667_, v___x_687_);
lean_dec(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___x_685_);
lean_dec(v_val_683_);
v___x_689_ = lean_box(0);
v___y_624_ = v___y_664_;
v___y_625_ = v___x_681_;
v___y_626_ = v___y_669_;
v___y_627_ = v___y_671_;
v___y_628_ = v___y_670_;
v___y_629_ = v___y_673_;
v___y_630_ = v___y_672_;
v___y_631_ = v_a_678_;
v___y_632_ = v___y_667_;
v___y_633_ = v___y_668_;
v_a_634_ = v___x_689_;
goto v___jp_623_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Lean_Elab_InfoTree_format(v_val_683_, v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v___x_693_ = l_Lean_MessageData_ofFormat(v_a_692_);
v___x_694_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_685_, v___x_693_, v___y_668_, v___y_670_);
v___y_650_ = v___y_664_;
v___y_651_ = v___x_681_;
v___y_652_ = v___y_669_;
v___y_653_ = v___y_670_;
v___y_654_ = v___y_671_;
v___y_655_ = v_a_678_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___y_667_;
v___y_659_ = v___y_668_;
v___y_660_ = v___x_694_;
goto v___jp_649_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
lean_dec(v___x_685_);
v_a_695_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v___x_691_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_691_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_io_error_to_string(v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 3);
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_704_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = l_Lean_MessageData_ofFormat(v___x_701_);
lean_inc(v___y_665_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_665_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___y_637_ = v___y_664_;
v___y_638_ = v___x_681_;
v___y_639_ = v___y_669_;
v___y_640_ = v___y_671_;
v___y_641_ = v___y_670_;
v___y_642_ = v___y_673_;
v___y_643_ = v___y_672_;
v___y_644_ = v_a_678_;
v___y_645_ = v___y_667_;
v___y_646_ = v___y_668_;
v_a_647_ = v___x_703_;
goto v___jp_636_;
}
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v___y_676_);
v___x_706_ = lean_box(0);
v___y_624_ = v___y_664_;
v___y_625_ = v___x_681_;
v___y_626_ = v___y_669_;
v___y_627_ = v___y_671_;
v___y_628_ = v___y_670_;
v___y_629_ = v___y_673_;
v___y_630_ = v___y_672_;
v___y_631_ = v_a_678_;
v___y_632_ = v___y_667_;
v___y_633_ = v___y_668_;
v_a_634_ = v___x_706_;
goto v___jp_623_;
}
}
else
{
lean_dec(v___y_676_);
v___y_650_ = v___y_664_;
v___y_651_ = v___x_681_;
v___y_652_ = v___y_669_;
v___y_653_ = v___y_670_;
v___y_654_ = v___y_671_;
v___y_655_ = v_a_678_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___y_667_;
v___y_659_ = v___y_668_;
v___y_660_ = v___x_682_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_io_get_num_heartbeats();
v___x_708_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_675_, v___y_668_, v___y_670_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_dec_ref(v___x_708_);
if (lean_obj_tag(v___y_676_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_val_709_ = lean_ctor_get(v___y_676_, 0);
lean_inc(v_val_709_);
lean_dec_ref(v___y_676_);
v___x_710_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_666_);
v___x_711_ = l_Lean_Name_mkStr2(v___y_666_, v___x_710_);
v___x_712_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_711_);
v___x_713_ = l_Lean_Name_append(v___x_712_, v___x_711_);
v___x_714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_674_, v___y_667_, v___x_713_);
lean_dec(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec(v___x_711_);
lean_dec(v_val_709_);
v___x_715_ = lean_box(0);
v___y_561_ = v___y_664_;
v___y_562_ = v___y_669_;
v___y_563_ = v___y_671_;
v___y_564_ = v___y_670_;
v___y_565_ = v___y_673_;
v___y_566_ = v___y_672_;
v___y_567_ = v_a_678_;
v___y_568_ = v___x_707_;
v___y_569_ = v___y_667_;
v___y_570_ = v___y_668_;
v_a_571_ = v___x_715_;
goto v___jp_560_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_Elab_InfoTree_format(v_val_709_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v___x_719_ = l_Lean_MessageData_ofFormat(v_a_718_);
v___x_720_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_711_, v___x_719_, v___y_668_, v___y_670_);
v___y_587_ = v___y_664_;
v___y_588_ = v___y_669_;
v___y_589_ = v___y_670_;
v___y_590_ = v___y_671_;
v___y_591_ = v_a_678_;
v___y_592_ = v___y_672_;
v___y_593_ = v___y_673_;
v___y_594_ = v___x_707_;
v___y_595_ = v___y_667_;
v___y_596_ = v___y_668_;
v___y_597_ = v___x_720_;
goto v___jp_586_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___x_711_);
v_a_721_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_731_ == 0)
{
v___x_723_ = v___x_717_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_io_error_to_string(v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 3);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_730_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l_Lean_MessageData_ofFormat(v___x_727_);
lean_inc(v___y_665_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___y_665_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___y_574_ = v___y_664_;
v___y_575_ = v___y_669_;
v___y_576_ = v___y_671_;
v___y_577_ = v___y_670_;
v___y_578_ = v___y_673_;
v___y_579_ = v___y_672_;
v___y_580_ = v_a_678_;
v___y_581_ = v___x_707_;
v___y_582_ = v___y_667_;
v___y_583_ = v___y_668_;
v_a_584_ = v___x_729_;
goto v___jp_573_;
}
}
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___y_676_);
v___x_732_ = lean_box(0);
v___y_561_ = v___y_664_;
v___y_562_ = v___y_669_;
v___y_563_ = v___y_671_;
v___y_564_ = v___y_670_;
v___y_565_ = v___y_673_;
v___y_566_ = v___y_672_;
v___y_567_ = v_a_678_;
v___y_568_ = v___x_707_;
v___y_569_ = v___y_667_;
v___y_570_ = v___y_668_;
v_a_571_ = v___x_732_;
goto v___jp_560_;
}
}
else
{
lean_dec(v___y_676_);
v___y_587_ = v___y_664_;
v___y_588_ = v___y_669_;
v___y_589_ = v___y_670_;
v___y_590_ = v___y_671_;
v___y_591_ = v_a_678_;
v___y_592_ = v___y_672_;
v___y_593_ = v___y_673_;
v___y_594_ = v___x_707_;
v___y_595_ = v___y_667_;
v___y_596_ = v___y_668_;
v___y_597_ = v___x_708_;
goto v___jp_586_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_664_);
v_a_733_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_677_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_677_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
v_resetjp_743_:
{
lean_object* v_desc_746_; lean_object* v_diagnostics_747_; lean_object* v_infoTree_x3f_748_; lean_object* v_desc_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___x_846_; 
v_desc_746_ = lean_ctor_get(v_element_741_, 0);
lean_inc_ref(v_desc_746_);
v_diagnostics_747_ = lean_ctor_get(v_element_741_, 1);
lean_inc_ref(v_diagnostics_747_);
v_infoTree_x3f_748_ = lean_ctor_get(v_element_741_, 2);
lean_inc(v_infoTree_x3f_748_);
lean_dec_ref(v_element_741_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v_desc_746_);
switch(lean_obj_tag(v_range_x3f_535_))
{
case 0:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v_desc_750_ = v___x_848_;
v___y_751_ = v_a_537_;
v___y_752_ = v_a_538_;
goto v___jp_749_;
}
case 1:
{
lean_object* v_range_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_907_; 
v_range_849_ = lean_ctor_get(v_range_x3f_535_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_range_x3f_535_);
if (v_isSharedCheck_907_ == 0)
{
v___x_851_ = v_range_x3f_535_;
v_isShared_852_ = v_isSharedCheck_907_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_range_849_);
lean_dec(v_range_x3f_535_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_907_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_fileMap_853_; lean_object* v_start_854_; lean_object* v_stop_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_906_; 
v_fileMap_853_ = lean_ctor_get(v_a_537_, 1);
v_start_854_ = lean_ctor_get(v_range_849_, 0);
v_stop_855_ = lean_ctor_get(v_range_849_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_range_849_);
if (v_isSharedCheck_906_ == 0)
{
v___x_857_ = v_range_849_;
v_isShared_858_ = v_isSharedCheck_906_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_stop_855_);
lean_inc(v_start_854_);
lean_dec(v_range_849_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_906_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v_line_860_; lean_object* v_column_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_905_; 
lean_inc_ref(v_fileMap_853_);
v___x_859_ = l_Lean_FileMap_toPosition(v_fileMap_853_, v_start_854_);
lean_dec(v_start_854_);
v_line_860_ = lean_ctor_get(v___x_859_, 0);
v_column_861_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_905_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_905_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_column_861_);
lean_inc(v_line_860_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_905_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v_line_866_; lean_object* v_column_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_904_; 
lean_inc_ref(v_fileMap_853_);
v___x_865_ = l_Lean_FileMap_toPosition(v_fileMap_853_, v_stop_855_);
lean_dec(v_stop_855_);
v_line_866_ = lean_ctor_get(v___x_865_, 0);
v_column_867_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_904_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_904_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_column_867_);
lean_inc(v_line_866_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_904_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_872_ = l_Nat_reprFast(v_line_860_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 3);
lean_ctor_set(v___x_851_, 0, v___x_872_);
v___x_874_ = v___x_851_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_903_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 5);
lean_ctor_set(v___x_869_, 1, v___x_874_);
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_876_ = v___x_869_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_902_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 5);
lean_ctor_set(v___x_863_, 1, v___x_877_);
lean_ctor_set(v___x_863_, 0, v___x_876_);
v___x_879_ = v___x_863_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_901_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = l_Nat_reprFast(v_column_861_);
v___x_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 5);
lean_ctor_set(v___x_857_, 1, v___x_881_);
lean_ctor_set(v___x_857_, 0, v___x_879_);
v___x_883_ = v___x_857_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_900_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Nat_reprFast(v_line_866_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_871_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_877_);
v___x_892_ = l_Nat_reprFast(v_column_867_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_891_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_884_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_887_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_846_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v_desc_750_ = v___x_899_;
v___y_751_ = v_a_537_;
v___y_752_ = v_a_538_;
goto v___jp_749_;
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
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_846_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v_desc_750_ = v___x_909_;
v___y_751_ = v_a_537_;
v___y_752_ = v_a_538_;
goto v___jp_749_;
}
}
v___jp_749_:
{
lean_object* v_msgLog_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_844_; 
v_msgLog_753_ = lean_ctor_get(v_diagnostics_747_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_diagnostics_747_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_diagnostics_747_, 1);
lean_dec(v_unused_845_);
v___x_755_ = v_diagnostics_747_;
v_isShared_756_ = v_isSharedCheck_844_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_msgLog_753_);
lean_dec(v_diagnostics_747_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_844_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_MessageLog_toList(v_msgLog_753_);
lean_dec_ref(v_msgLog_753_);
v___x_758_ = lean_box(0);
v___x_759_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_757_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_options_760_; lean_object* v_a_761_; lean_object* v_ref_762_; lean_object* v_inheritedTraceOptions_763_; uint8_t v_hasTrace_764_; lean_object* v___x_765_; 
v_options_760_ = lean_ctor_get(v___y_751_, 2);
v_a_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v___x_759_);
v_ref_762_ = lean_ctor_get(v___y_751_, 5);
v_inheritedTraceOptions_763_ = lean_ctor_get(v___y_751_, 13);
v_hasTrace_764_ = lean_ctor_get_uint8(v_options_760_, sizeof(void*)*1);
v___x_765_ = lean_array_to_list(v_children_742_);
if (v_hasTrace_764_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v_a_761_);
lean_del_object(v___x_755_);
lean_dec(v_desc_750_);
lean_del_object(v___x_744_);
v___x_766_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_765_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_778_; 
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_766_, 0);
lean_dec(v_unused_779_);
v___x_768_ = v___x_766_;
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
else
{
lean_dec(v___x_766_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_infoTree_x3f_748_) == 1)
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec_ref(v_infoTree_x3f_748_);
v___x_770_ = lean_box(0);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec(v_infoTree_x3f_748_);
v___x_774_ = lean_box(0);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_774_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_748_);
return v___x_766_;
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_781_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_782_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_781_, v_a_761_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 5);
lean_ctor_set(v___x_755_, 1, v___x_782_);
lean_ctor_set(v___x_755_, 0, v_desc_750_);
v___x_784_ = v___x_755_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_desc_750_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_835_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___f_785_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_785_, 0, v___x_784_);
v___x_786_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_787_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_788_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_760_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = l_Lean_trace_profiler;
v___x_791_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_760_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v___f_785_);
v___x_792_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_765_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_834_);
v___x_794_ = v___x_792_;
v_isShared_795_ = v_isSharedCheck_833_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_792_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_833_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_infoTree_x3f_748_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_828_; 
v_val_796_ = lean_ctor_get(v_infoTree_x3f_748_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_infoTree_x3f_748_);
if (v_isSharedCheck_828_ == 0)
{
v___x_798_ = v_infoTree_x3f_748_;
v_isShared_799_ = v_isSharedCheck_828_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v_infoTree_x3f_748_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_828_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_801_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_760_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_del_object(v___x_798_);
lean_dec(v_val_796_);
lean_del_object(v___x_744_);
v___x_803_ = lean_box(0);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_803_);
v___x_805_ = v___x_794_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_794_);
v___x_807_ = lean_box(0);
v___x_808_ = l_Lean_Elab_InfoTree_format(v_val_796_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_798_);
lean_del_object(v___x_744_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_MessageData_ofFormat(v_a_809_);
v___x_811_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_800_, v___x_810_, v___y_751_, v___y_752_);
return v___x_811_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_827_; 
v_a_812_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_827_ == 0)
{
v___x_814_ = v___x_808_;
v_isShared_815_ = v_isSharedCheck_827_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_827_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_io_error_to_string(v_a_812_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 3);
lean_ctor_set(v___x_798_, 0, v___x_816_);
v___x_818_ = v___x_798_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_826_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_MessageData_ofFormat(v___x_818_);
lean_inc(v_ref_762_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_819_);
lean_ctor_set(v___x_744_, 0, v_ref_762_);
v___x_821_ = v___x_744_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_ref_762_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_821_);
v___x_823_ = v___x_814_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
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
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec(v_infoTree_x3f_748_);
lean_del_object(v___x_744_);
v___x_829_ = lean_box(0);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_829_);
v___x_831_ = v___x_794_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_748_);
lean_del_object(v___x_744_);
return v___x_792_;
}
}
else
{
lean_del_object(v___x_744_);
v___y_664_ = v___f_785_;
v___y_665_ = v_ref_762_;
v___y_666_ = v___x_780_;
v___y_667_ = v_options_760_;
v___y_668_ = v___y_751_;
v___y_669_ = v___x_789_;
v___y_670_ = v___y_752_;
v___y_671_ = v_hasTrace_764_;
v___y_672_ = v___x_787_;
v___y_673_ = v___x_786_;
v___y_674_ = v_inheritedTraceOptions_763_;
v___y_675_ = v___x_765_;
v___y_676_ = v_infoTree_x3f_748_;
goto v___jp_663_;
}
}
else
{
lean_del_object(v___x_744_);
v___y_664_ = v___f_785_;
v___y_665_ = v_ref_762_;
v___y_666_ = v___x_780_;
v___y_667_ = v_options_760_;
v___y_668_ = v___y_751_;
v___y_669_ = v___x_789_;
v___y_670_ = v___y_752_;
v___y_671_ = v_hasTrace_764_;
v___y_672_ = v___x_787_;
v___y_673_ = v___x_786_;
v___y_674_ = v_inheritedTraceOptions_763_;
v___y_675_ = v___x_765_;
v___y_676_ = v_infoTree_x3f_748_;
goto v___jp_663_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_755_);
lean_dec(v_desc_750_);
lean_dec(v_infoTree_x3f_748_);
lean_del_object(v___x_744_);
lean_dec_ref(v_children_742_);
v_a_836_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_759_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_759_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
if (lean_obj_tag(v_as_911_) == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
else
{
lean_object* v_head_917_; lean_object* v_tail_918_; lean_object* v_reportingRange_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_head_917_ = lean_ctor_get(v_as_911_, 0);
lean_inc(v_head_917_);
v_tail_918_ = lean_ctor_get(v_as_911_, 1);
lean_inc(v_tail_918_);
lean_dec_ref(v_as_911_);
v_reportingRange_919_ = lean_ctor_get(v_head_917_, 1);
lean_inc(v_reportingRange_919_);
v___x_920_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_917_);
v___x_921_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_919_, v___x_920_, v___y_912_, v___y_913_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref(v___x_921_);
v_as_911_ = v_tail_918_;
goto _start;
}
else
{
lean_dec(v_tail_918_);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_928_, lean_object* v_s_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_928_, v_s_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_934_, v_x_935_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_940_, v_x_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_00_u03b1_946_, lean_object* v_x_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_947_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_00_u03b1_952_, lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_00_u03b1_952_, v_x_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_box(2);
v___x_963_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_962_, v_s_958_, v_a_959_, v_a_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Language_SnapshotTree_trace(v_s_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_968_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

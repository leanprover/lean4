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
lean_object* v___x_12_; lean_object* v_traceState_13_; lean_object* v_traces_14_; lean_object* v___x_15_; lean_object* v_traceState_16_; lean_object* v_env_17_; lean_object* v_nextMacroScope_18_; lean_object* v_ngen_19_; lean_object* v_auxDeclNGen_20_; lean_object* v_cache_21_; lean_object* v_messages_22_; lean_object* v_infoState_23_; lean_object* v_snapshotTasks_24_; lean_object* v_newDecls_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_44_; 
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
v_newDecls_25_ = lean_ctor_get(v___x_15_, 9);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_44_ == 0)
{
v___x_27_ = v___x_15_;
v_isShared_28_ = v_isSharedCheck_44_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_newDecls_25_);
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
lean_ctor_set(v_reuseFailAlloc_40_, 6, v_messages_22_);
lean_ctor_set(v_reuseFailAlloc_40_, 7, v_infoState_23_);
lean_ctor_set(v_reuseFailAlloc_40_, 8, v_snapshotTasks_24_);
lean_ctor_set(v_reuseFailAlloc_40_, 9, v_newDecls_25_);
v___x_37_ = v_reuseFailAlloc_40_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_st_ref_set(v___y_10_, v___x_37_);
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
lean_dec_ref(v___x_61_);
if (lean_obj_tag(v_val_63_) == 1)
{
uint8_t v_v_64_; 
v_v_64_ = lean_ctor_get_uint8(v_val_63_, 0);
lean_dec_ref(v_val_63_);
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
v___x_83_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_88_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v_options_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v_options_108_ = lean_ctor_get(v___y_103_, 2);
v___x_109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_108_);
v___x_111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_111_, 0, v_env_107_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
lean_ctor_set(v___x_111_, 3, v_options_108_);
v___x_112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_msgData_102_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_118_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_119_; double v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_float_of_nat(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_124_, lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_176_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 5);
v___x_130_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_176_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_176_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_176_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v_traceState_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_cache_141_; lean_object* v_messages_142_; lean_object* v_infoState_143_; lean_object* v_snapshotTasks_144_; lean_object* v_newDecls_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_175_; 
v___x_135_ = lean_st_ref_take(v___y_127_);
v_traceState_136_ = lean_ctor_get(v___x_135_, 4);
v_env_137_ = lean_ctor_get(v___x_135_, 0);
v_nextMacroScope_138_ = lean_ctor_get(v___x_135_, 1);
v_ngen_139_ = lean_ctor_get(v___x_135_, 2);
v_auxDeclNGen_140_ = lean_ctor_get(v___x_135_, 3);
v_cache_141_ = lean_ctor_get(v___x_135_, 5);
v_messages_142_ = lean_ctor_get(v___x_135_, 6);
v_infoState_143_ = lean_ctor_get(v___x_135_, 7);
v_snapshotTasks_144_ = lean_ctor_get(v___x_135_, 8);
v_newDecls_145_ = lean_ctor_get(v___x_135_, 9);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_175_ == 0)
{
v___x_147_ = v___x_135_;
v_isShared_148_ = v_isSharedCheck_175_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_newDecls_145_);
lean_inc(v_snapshotTasks_144_);
lean_inc(v_infoState_143_);
lean_inc(v_messages_142_);
lean_inc(v_cache_141_);
lean_inc(v_traceState_136_);
lean_inc(v_auxDeclNGen_140_);
lean_inc(v_ngen_139_);
lean_inc(v_nextMacroScope_138_);
lean_inc(v_env_137_);
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_175_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint64_t v_tid_149_; lean_object* v_traces_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_174_; 
v_tid_149_ = lean_ctor_get_uint64(v_traceState_136_, sizeof(void*)*1);
v_traces_150_ = lean_ctor_get(v_traceState_136_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_traceState_136_);
if (v_isSharedCheck_174_ == 0)
{
v___x_152_ = v_traceState_136_;
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_traces_150_);
lean_dec(v_traceState_136_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; double v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_156_ = 0;
v___x_157_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_158_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_158_, 0, v_cls_124_);
lean_ctor_set(v___x_158_, 1, v___x_154_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set_float(v___x_158_, sizeof(void*)*3, v___x_155_);
lean_ctor_set_float(v___x_158_, sizeof(void*)*3 + 8, v___x_155_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*3 + 16, v___x_156_);
v___x_159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_160_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v_a_131_);
lean_ctor_set(v___x_160_, 2, v___x_159_);
lean_inc(v_ref_129_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_ref_129_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_PersistentArray_push___redArg(v_traces_150_, v___x_161_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_162_);
v___x_164_ = v___x_152_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_162_);
lean_ctor_set_uint64(v_reuseFailAlloc_173_, sizeof(void*)*1, v_tid_149_);
v___x_164_ = v_reuseFailAlloc_173_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 4, v___x_164_);
v___x_166_ = v___x_147_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_env_137_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 5, v_cache_141_);
lean_ctor_set(v_reuseFailAlloc_172_, 6, v_messages_142_);
lean_ctor_set(v_reuseFailAlloc_172_, 7, v_infoState_143_);
lean_ctor_set(v_reuseFailAlloc_172_, 8, v_snapshotTasks_144_);
lean_ctor_set(v_reuseFailAlloc_172_, 9, v_newDecls_145_);
v___x_166_ = v_reuseFailAlloc_172_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = lean_st_ref_set(v___y_127_, v___x_166_);
v___x_168_ = lean_box(0);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_168_);
v___x_170_ = v___x_133_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_177_, lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_177_, v_msg_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_dec(v_pre_183_);
return v_x_184_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_head_186_ = lean_ctor_get(v_x_185_, 0);
v_tail_187_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_197_ == 0)
{
v___x_189_ = v_x_185_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_tail_187_);
lean_inc(v_head_186_);
lean_dec(v_x_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
lean_inc(v_pre_183_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 5);
lean_ctor_set(v___x_189_, 1, v_pre_183_);
lean_ctor_set(v___x_189_, 0, v_x_184_);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_x_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_pre_183_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_193_, 0, v_head_186_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v_x_184_ = v___x_194_;
v_x_185_ = v_tail_187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v_pre_198_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_211_; 
v_head_201_ = lean_ctor_get(v_x_199_, 0);
v_tail_202_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_211_ == 0)
{
v___x_204_ = v_x_199_;
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_tail_202_);
lean_inc(v_head_201_);
lean_dec(v_x_199_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_206_, 0, v_head_201_);
lean_inc(v_pre_198_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 5);
lean_ctor_set(v___x_204_, 1, v___x_206_);
lean_ctor_set(v___x_204_, 0, v_pre_198_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_pre_198_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_198_, v___x_208_, v_tail_202_);
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = l_List_reverse___redArg(v_x_213_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_head_217_; lean_object* v_tail_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
v_head_217_ = lean_ctor_get(v_x_212_, 0);
v_tail_218_ = lean_ctor_get(v_x_212_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_228_ == 0)
{
v___x_220_ = v_x_212_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_tail_218_);
lean_inc(v_head_217_);
lean_dec(v_x_212_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = 0;
v___x_223_ = l_Lean_Message_toString(v_head_217_, v___x_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_x_213_);
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_x_213_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
v_x_212_ = v_tail_218_;
v_x_213_ = v___x_225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_229_, v_x_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(size_t v_sz_233_, size_t v_i_234_, lean_object* v_bs_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_236_ == 0)
{
return v_bs_235_;
}
else
{
lean_object* v_v_237_; lean_object* v_msg_238_; lean_object* v___x_239_; lean_object* v_bs_x27_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v_v_237_ = lean_array_uget_borrowed(v_bs_235_, v_i_234_);
v_msg_238_ = lean_ctor_get(v_v_237_, 1);
lean_inc_ref(v_msg_238_);
v___x_239_ = lean_unsigned_to_nat(0u);
v_bs_x27_240_ = lean_array_uset(v_bs_235_, v_i_234_, v___x_239_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_234_, v___x_241_);
v___x_243_ = lean_array_uset(v_bs_x27_240_, v_i_234_, v_msg_238_);
v_i_234_ = v___x_242_;
v_bs_235_ = v___x_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_245_, lean_object* v_i_246_, lean_object* v_bs_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_245_);
lean_dec(v_sz_245_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_boxed_248_, v_i_boxed_249_, v_bs_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_oldTraces_251_, lean_object* v_data_252_, lean_object* v_ref_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_fileName_258_; lean_object* v_fileMap_259_; lean_object* v_options_260_; lean_object* v_currRecDepth_261_; lean_object* v_maxRecDepth_262_; lean_object* v_ref_263_; lean_object* v_currNamespace_264_; lean_object* v_openDecls_265_; lean_object* v_initHeartbeats_266_; lean_object* v_maxHeartbeats_267_; lean_object* v_quotContext_268_; lean_object* v_currMacroScope_269_; uint8_t v_diag_270_; lean_object* v_cancelTk_x3f_271_; uint8_t v_suppressElabErrors_272_; lean_object* v_inheritedTraceOptions_273_; lean_object* v___x_274_; lean_object* v_traceState_275_; lean_object* v_traces_276_; lean_object* v_ref_277_; lean_object* v___x_278_; lean_object* v___x_279_; size_t v_sz_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v_msg_283_; lean_object* v___x_284_; lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_323_; 
v_fileName_258_ = lean_ctor_get(v___y_255_, 0);
v_fileMap_259_ = lean_ctor_get(v___y_255_, 1);
v_options_260_ = lean_ctor_get(v___y_255_, 2);
v_currRecDepth_261_ = lean_ctor_get(v___y_255_, 3);
v_maxRecDepth_262_ = lean_ctor_get(v___y_255_, 4);
v_ref_263_ = lean_ctor_get(v___y_255_, 5);
v_currNamespace_264_ = lean_ctor_get(v___y_255_, 6);
v_openDecls_265_ = lean_ctor_get(v___y_255_, 7);
v_initHeartbeats_266_ = lean_ctor_get(v___y_255_, 8);
v_maxHeartbeats_267_ = lean_ctor_get(v___y_255_, 9);
v_quotContext_268_ = lean_ctor_get(v___y_255_, 10);
v_currMacroScope_269_ = lean_ctor_get(v___y_255_, 11);
v_diag_270_ = lean_ctor_get_uint8(v___y_255_, sizeof(void*)*14);
v_cancelTk_x3f_271_ = lean_ctor_get(v___y_255_, 12);
v_suppressElabErrors_272_ = lean_ctor_get_uint8(v___y_255_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_273_ = lean_ctor_get(v___y_255_, 13);
v___x_274_ = lean_st_ref_get(v___y_256_);
v_traceState_275_ = lean_ctor_get(v___x_274_, 4);
lean_inc_ref(v_traceState_275_);
lean_dec(v___x_274_);
v_traces_276_ = lean_ctor_get(v_traceState_275_, 0);
lean_inc_ref(v_traces_276_);
lean_dec_ref(v_traceState_275_);
v_ref_277_ = l_Lean_replaceRef(v_ref_253_, v_ref_263_);
lean_inc_ref(v_inheritedTraceOptions_273_);
lean_inc(v_cancelTk_x3f_271_);
lean_inc(v_currMacroScope_269_);
lean_inc(v_quotContext_268_);
lean_inc(v_maxHeartbeats_267_);
lean_inc(v_initHeartbeats_266_);
lean_inc(v_openDecls_265_);
lean_inc(v_currNamespace_264_);
lean_inc(v_maxRecDepth_262_);
lean_inc(v_currRecDepth_261_);
lean_inc_ref(v_options_260_);
lean_inc_ref(v_fileMap_259_);
lean_inc_ref(v_fileName_258_);
v___x_278_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_278_, 0, v_fileName_258_);
lean_ctor_set(v___x_278_, 1, v_fileMap_259_);
lean_ctor_set(v___x_278_, 2, v_options_260_);
lean_ctor_set(v___x_278_, 3, v_currRecDepth_261_);
lean_ctor_set(v___x_278_, 4, v_maxRecDepth_262_);
lean_ctor_set(v___x_278_, 5, v_ref_277_);
lean_ctor_set(v___x_278_, 6, v_currNamespace_264_);
lean_ctor_set(v___x_278_, 7, v_openDecls_265_);
lean_ctor_set(v___x_278_, 8, v_initHeartbeats_266_);
lean_ctor_set(v___x_278_, 9, v_maxHeartbeats_267_);
lean_ctor_set(v___x_278_, 10, v_quotContext_268_);
lean_ctor_set(v___x_278_, 11, v_currMacroScope_269_);
lean_ctor_set(v___x_278_, 12, v_cancelTk_x3f_271_);
lean_ctor_set(v___x_278_, 13, v_inheritedTraceOptions_273_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*14, v_diag_270_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*14 + 1, v_suppressElabErrors_272_);
v___x_279_ = l_Lean_PersistentArray_toArray___redArg(v_traces_276_);
lean_dec_ref(v_traces_276_);
v_sz_280_ = lean_array_size(v___x_279_);
v___x_281_ = ((size_t)0ULL);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9_spec__10(v_sz_280_, v___x_281_, v___x_279_);
v_msg_283_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_283_, 0, v_data_252_);
lean_ctor_set(v_msg_283_, 1, v_msg_254_);
lean_ctor_set(v_msg_283_, 2, v___x_282_);
v___x_284_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_283_, v___x_278_, v___y_256_);
lean_dec_ref(v___x_278_);
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_323_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_323_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_323_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v_traceState_290_; lean_object* v_env_291_; lean_object* v_nextMacroScope_292_; lean_object* v_ngen_293_; lean_object* v_auxDeclNGen_294_; lean_object* v_cache_295_; lean_object* v_messages_296_; lean_object* v_infoState_297_; lean_object* v_snapshotTasks_298_; lean_object* v_newDecls_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_322_; 
v___x_289_ = lean_st_ref_take(v___y_256_);
v_traceState_290_ = lean_ctor_get(v___x_289_, 4);
v_env_291_ = lean_ctor_get(v___x_289_, 0);
v_nextMacroScope_292_ = lean_ctor_get(v___x_289_, 1);
v_ngen_293_ = lean_ctor_get(v___x_289_, 2);
v_auxDeclNGen_294_ = lean_ctor_get(v___x_289_, 3);
v_cache_295_ = lean_ctor_get(v___x_289_, 5);
v_messages_296_ = lean_ctor_get(v___x_289_, 6);
v_infoState_297_ = lean_ctor_get(v___x_289_, 7);
v_snapshotTasks_298_ = lean_ctor_get(v___x_289_, 8);
v_newDecls_299_ = lean_ctor_get(v___x_289_, 9);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_322_ == 0)
{
v___x_301_ = v___x_289_;
v_isShared_302_ = v_isSharedCheck_322_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_newDecls_299_);
lean_inc(v_snapshotTasks_298_);
lean_inc(v_infoState_297_);
lean_inc(v_messages_296_);
lean_inc(v_cache_295_);
lean_inc(v_traceState_290_);
lean_inc(v_auxDeclNGen_294_);
lean_inc(v_ngen_293_);
lean_inc(v_nextMacroScope_292_);
lean_inc(v_env_291_);
lean_dec(v___x_289_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_322_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint64_t v_tid_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_320_; 
v_tid_303_ = lean_ctor_get_uint64(v_traceState_290_, sizeof(void*)*1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_traceState_290_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v_traceState_290_, 0);
lean_dec(v_unused_321_);
v___x_305_ = v_traceState_290_;
v_isShared_306_ = v_isSharedCheck_320_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_traceState_290_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_320_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_ref_253_);
lean_ctor_set(v___x_307_, 1, v_a_285_);
v___x_308_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_251_, v___x_307_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_308_);
lean_ctor_set_uint64(v_reuseFailAlloc_319_, sizeof(void*)*1, v_tid_303_);
v___x_310_ = v_reuseFailAlloc_319_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 4, v___x_310_);
v___x_312_ = v___x_301_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_env_291_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_nextMacroScope_292_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_ngen_293_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_auxDeclNGen_294_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_cache_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_messages_296_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_infoState_297_);
lean_ctor_set(v_reuseFailAlloc_318_, 8, v_snapshotTasks_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 9, v_newDecls_299_);
v___x_312_ = v_reuseFailAlloc_318_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_st_ref_set(v___y_256_, v___x_312_);
v___x_314_ = lean_box(0);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_314_);
v___x_316_ = v___x_287_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_oldTraces_324_, lean_object* v_data_325_, lean_object* v_ref_326_, lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_324_, v_data_325_, v_ref_326_, v_msg_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_332_, lean_object* v_opt_333_){
_start:
{
lean_object* v_name_334_; lean_object* v_defValue_335_; lean_object* v_map_336_; lean_object* v___x_337_; 
v_name_334_ = lean_ctor_get(v_opt_333_, 0);
v_defValue_335_ = lean_ctor_get(v_opt_333_, 1);
v_map_336_ = lean_ctor_get(v_opts_332_, 0);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_336_, v_name_334_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_inc(v_defValue_335_);
return v_defValue_335_;
}
else
{
lean_object* v_val_338_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref(v___x_337_);
if (lean_obj_tag(v_val_338_) == 3)
{
lean_object* v_v_339_; 
v_v_339_ = lean_ctor_get(v_val_338_, 0);
lean_inc(v_v_339_);
lean_dec_ref(v_val_338_);
return v_v_339_;
}
else
{
lean_dec(v_val_338_);
lean_inc(v_defValue_335_);
return v_defValue_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_340_, lean_object* v_opt_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_340_, v_opt_341_);
lean_dec_ref(v_opt_341_);
lean_dec_ref(v_opts_340_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_e_343_){
_start:
{
if (lean_obj_tag(v_e_343_) == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 2;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_e_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_e_346_);
lean_dec_ref(v_e_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v_x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v_x_349_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v_x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v_x_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v_x_349_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v_x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 0);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg___boxed(lean_object* v_x_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_367_);
return v_res_369_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4(void){
_start:
{
lean_object* v___x_376_; double v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1000u);
v___x_377_ = lean_float_of_nat(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_378_, uint8_t v_collapsed_379_, lean_object* v_tag_380_, lean_object* v_opts_381_, uint8_t v_clsEnabled_382_, lean_object* v_oldTraces_383_, lean_object* v_msg_384_, lean_object* v_resStartStop_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_481_; 
v_fst_389_ = lean_ctor_get(v_resStartStop_385_, 0);
v_snd_390_ = lean_ctor_get(v_resStartStop_385_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_resStartStop_385_);
if (v_isSharedCheck_481_ == 0)
{
v___x_392_ = v_resStartStop_385_;
v_isShared_393_ = v_isSharedCheck_481_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_inc(v_fst_389_);
lean_dec(v_resStartStop_385_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_481_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v_data_397_; lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_480_; 
v_fst_400_ = lean_ctor_get(v_snd_390_, 0);
v_snd_401_ = lean_ctor_get(v_snd_390_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_snd_390_);
if (v_isSharedCheck_480_ == 0)
{
v___x_403_ = v_snd_390_;
v_isShared_404_ = v_isSharedCheck_480_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v_snd_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_480_;
goto v_resetjp_402_;
}
v___jp_394_:
{
lean_object* v___x_398_; 
lean_inc(v___y_395_);
v___x_398_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_oldTraces_383_, v_data_397_, v___y_395_, v___y_396_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v___x_398_);
v___x_399_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_389_);
return v___x_399_;
}
else
{
lean_dec(v_fst_389_);
return v___x_398_;
}
}
v_resetjp_402_:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___y_408_; lean_object* v_a_409_; uint8_t v___y_433_; double v___y_465_; 
v___x_405_ = l_Lean_trace_profiler;
v___x_406_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_381_, v___x_405_);
if (v___x_406_ == 0)
{
v___y_433_ = v___x_406_;
goto v___jp_432_;
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = l_Lean_trace_profiler_useHeartbeats;
v___x_471_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_381_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; double v___x_474_; double v___x_475_; double v___x_476_; 
v___x_472_ = l_Lean_trace_profiler_threshold;
v___x_473_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_381_, v___x_472_);
v___x_474_ = lean_float_of_nat(v___x_473_);
v___x_475_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__4);
v___x_476_ = lean_float_div(v___x_474_, v___x_475_);
v___y_465_ = v___x_476_;
goto v___jp_464_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; double v___x_479_; 
v___x_477_ = l_Lean_trace_profiler_threshold;
v___x_478_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_381_, v___x_477_);
v___x_479_ = lean_float_of_nat(v___x_478_);
v___y_465_ = v___x_479_;
goto v___jp_464_;
}
}
v___jp_407_:
{
uint8_t v_result_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_result_410_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_fst_389_);
v___x_411_ = l_Lean_TraceResult_toEmoji(v_result_410_);
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
v___x_413_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 7);
lean_ctor_set(v___x_403_, 1, v___x_413_);
lean_ctor_set(v___x_403_, 0, v___x_412_);
v___x_415_ = v___x_403_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_426_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v_m_417_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 7);
lean_ctor_set(v___x_392_, 1, v_a_409_);
lean_ctor_set(v___x_392_, 0, v___x_415_);
v_m_417_ = v___x_392_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_409_);
v_m_417_ = v_reuseFailAlloc_425_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; double v___x_420_; lean_object* v_data_421_; 
v___x_418_ = lean_box(v_result_410_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
v___x_420_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_380_);
lean_inc_ref(v___x_419_);
lean_inc(v_cls_378_);
v_data_421_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_421_, 0, v_cls_378_);
lean_ctor_set(v_data_421_, 1, v___x_419_);
lean_ctor_set(v_data_421_, 2, v_tag_380_);
lean_ctor_set_float(v_data_421_, sizeof(void*)*3, v___x_420_);
lean_ctor_set_float(v_data_421_, sizeof(void*)*3 + 8, v___x_420_);
lean_ctor_set_uint8(v_data_421_, sizeof(void*)*3 + 16, v_collapsed_379_);
if (v___x_406_ == 0)
{
lean_dec_ref(v___x_419_);
lean_dec(v_snd_401_);
lean_dec(v_fst_400_);
lean_dec_ref(v_tag_380_);
lean_dec(v_cls_378_);
v___y_395_ = v___y_408_;
v___y_396_ = v_m_417_;
v_data_397_ = v_data_421_;
goto v___jp_394_;
}
else
{
lean_object* v_data_422_; double v___x_423_; double v___x_424_; 
lean_dec_ref(v_data_421_);
v_data_422_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_422_, 0, v_cls_378_);
lean_ctor_set(v_data_422_, 1, v___x_419_);
lean_ctor_set(v_data_422_, 2, v_tag_380_);
v___x_423_ = lean_unbox_float(v_fst_400_);
lean_dec(v_fst_400_);
lean_ctor_set_float(v_data_422_, sizeof(void*)*3, v___x_423_);
v___x_424_ = lean_unbox_float(v_snd_401_);
lean_dec(v_snd_401_);
lean_ctor_set_float(v_data_422_, sizeof(void*)*3 + 8, v___x_424_);
lean_ctor_set_uint8(v_data_422_, sizeof(void*)*3 + 16, v_collapsed_379_);
v___y_395_ = v___y_408_;
v___y_396_ = v_m_417_;
v_data_397_ = v_data_422_;
goto v___jp_394_;
}
}
}
}
v___jp_427_:
{
lean_object* v_ref_428_; lean_object* v___x_429_; 
v_ref_428_ = lean_ctor_get(v___y_386_, 5);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v_fst_389_);
v___x_429_ = lean_apply_4(v_msg_384_, v_fst_389_, v___y_386_, v___y_387_, lean_box(0));
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v___y_408_ = v_ref_428_;
v_a_409_ = v_a_430_;
goto v___jp_407_;
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v___x_429_);
v___x_431_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__3);
v___y_408_ = v_ref_428_;
v_a_409_ = v___x_431_;
goto v___jp_407_;
}
}
v___jp_432_:
{
if (v_clsEnabled_382_ == 0)
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v_traceState_435_; lean_object* v_env_436_; lean_object* v_nextMacroScope_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_cache_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v_newDecls_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_403_);
lean_dec(v_snd_401_);
lean_dec(v_fst_400_);
lean_del_object(v___x_392_);
lean_dec_ref(v_msg_384_);
lean_dec_ref(v_tag_380_);
lean_dec(v_cls_378_);
v___x_434_ = lean_st_ref_take(v___y_387_);
v_traceState_435_ = lean_ctor_get(v___x_434_, 4);
v_env_436_ = lean_ctor_get(v___x_434_, 0);
v_nextMacroScope_437_ = lean_ctor_get(v___x_434_, 1);
v_ngen_438_ = lean_ctor_get(v___x_434_, 2);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_434_, 3);
v_cache_440_ = lean_ctor_get(v___x_434_, 5);
v_messages_441_ = lean_ctor_get(v___x_434_, 6);
v_infoState_442_ = lean_ctor_get(v___x_434_, 7);
v_snapshotTasks_443_ = lean_ctor_get(v___x_434_, 8);
v_newDecls_444_ = lean_ctor_get(v___x_434_, 9);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_463_ == 0)
{
v___x_446_ = v___x_434_;
v_isShared_447_ = v_isSharedCheck_463_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_newDecls_444_);
lean_inc(v_snapshotTasks_443_);
lean_inc(v_infoState_442_);
lean_inc(v_messages_441_);
lean_inc(v_cache_440_);
lean_inc(v_traceState_435_);
lean_inc(v_auxDeclNGen_439_);
lean_inc(v_ngen_438_);
lean_inc(v_nextMacroScope_437_);
lean_inc(v_env_436_);
lean_dec(v___x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_463_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint64_t v_tid_448_; lean_object* v_traces_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_462_; 
v_tid_448_ = lean_ctor_get_uint64(v_traceState_435_, sizeof(void*)*1);
v_traces_449_ = lean_ctor_get(v_traceState_435_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_traceState_435_);
if (v_isSharedCheck_462_ == 0)
{
v___x_451_ = v_traceState_435_;
v_isShared_452_ = v_isSharedCheck_462_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_traces_449_);
lean_dec(v_traceState_435_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_462_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_383_, v_traces_449_);
lean_dec_ref(v_traces_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_453_);
lean_ctor_set_uint64(v_reuseFailAlloc_461_, sizeof(void*)*1, v_tid_448_);
v___x_455_ = v_reuseFailAlloc_461_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 4, v___x_455_);
v___x_457_ = v___x_446_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_env_436_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_nextMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_ngen_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_460_, 5, v_cache_440_);
lean_ctor_set(v_reuseFailAlloc_460_, 6, v_messages_441_);
lean_ctor_set(v_reuseFailAlloc_460_, 7, v_infoState_442_);
lean_ctor_set(v_reuseFailAlloc_460_, 8, v_snapshotTasks_443_);
lean_ctor_set(v_reuseFailAlloc_460_, 9, v_newDecls_444_);
v___x_457_ = v_reuseFailAlloc_460_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_st_ref_set(v___y_387_, v___x_457_);
v___x_459_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_fst_389_);
return v___x_459_;
}
}
}
}
}
else
{
goto v___jp_427_;
}
}
else
{
goto v___jp_427_;
}
}
v___jp_464_:
{
double v___x_466_; double v___x_467_; double v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_unbox_float(v_snd_401_);
v___x_467_ = lean_unbox_float(v_fst_400_);
v___x_468_ = lean_float_sub(v___x_466_, v___x_467_);
v___x_469_ = lean_float_decLt(v___y_465_, v___x_468_);
v___y_433_ = v___x_469_;
goto v___jp_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_482_, lean_object* v_collapsed_483_, lean_object* v_tag_484_, lean_object* v_opts_485_, lean_object* v_clsEnabled_486_, lean_object* v_oldTraces_487_, lean_object* v_msg_488_, lean_object* v_resStartStop_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v_collapsed_boxed_493_; uint8_t v_clsEnabled_boxed_494_; lean_object* v_res_495_; 
v_collapsed_boxed_493_ = lean_unbox(v_collapsed_483_);
v_clsEnabled_boxed_494_ = lean_unbox(v_clsEnabled_486_);
v_res_495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_482_, v_collapsed_boxed_493_, v_tag_484_, v_opts_485_, v_clsEnabled_boxed_494_, v_oldTraces_487_, v_msg_488_, v_resStartStop_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v_opts_485_);
return v_res_495_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_496_; double v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(1000000000u);
v___x_497_ = lean_float_of_nat(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_511_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_512_ = l_Lean_Name_append(v___x_511_, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_517_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_518_ = l_Lean_Name_append(v___x_517_, v___x_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_539_, lean_object* v_s_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v_a_555_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v_a_575_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v_a_588_; uint8_t v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; uint8_t v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v_a_615_; uint8_t v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v_a_638_; uint8_t v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v_a_651_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v_element_745_; lean_object* v_children_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_914_; 
v_element_745_ = lean_ctor_get(v_s_540_, 0);
v_children_746_ = lean_ctor_get(v_s_540_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_s_540_);
if (v_isSharedCheck_914_ == 0)
{
v___x_748_ = v_s_540_;
v_isShared_749_ = v_isSharedCheck_914_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_children_746_);
lean_inc(v_element_745_);
lean_dec(v_s_540_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_914_;
goto v_resetjp_747_;
}
v___jp_544_:
{
lean_object* v___x_556_; double v___x_557_; double v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_556_ = lean_io_get_num_heartbeats();
v___x_557_ = lean_float_of_nat(v___y_551_);
v___x_558_ = lean_float_of_nat(v___x_556_);
v___x_559_ = lean_box_float(v___x_557_);
v___x_560_ = lean_box_float(v___x_558_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_a_555_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
v___x_563_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_547_, v___y_545_, v___y_548_, v___y_546_, v___y_550_, v___y_554_, v___y_552_, v___x_562_, v___y_553_, v___y_549_);
return v___x_563_;
}
v___jp_564_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_a_575_);
v___y_545_ = v___y_565_;
v___y_546_ = v___y_566_;
v___y_547_ = v___y_567_;
v___y_548_ = v___y_568_;
v___y_549_ = v___y_569_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_571_;
v___y_552_ = v___y_572_;
v___y_553_ = v___y_573_;
v___y_554_ = v___y_574_;
v_a_555_ = v___x_576_;
goto v___jp_544_;
}
v___jp_577_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_a_588_);
v___y_545_ = v___y_578_;
v___y_546_ = v___y_579_;
v___y_547_ = v___y_580_;
v___y_548_ = v___y_581_;
v___y_549_ = v___y_582_;
v___y_550_ = v___y_583_;
v___y_551_ = v___y_584_;
v___y_552_ = v___y_585_;
v___y_553_ = v___y_586_;
v___y_554_ = v___y_587_;
v_a_555_ = v___x_589_;
goto v___jp_544_;
}
v___jp_590_:
{
if (lean_obj_tag(v___y_601_) == 0)
{
lean_object* v_a_602_; 
v_a_602_ = lean_ctor_get(v___y_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___y_601_);
v___y_565_ = v___y_591_;
v___y_566_ = v___y_592_;
v___y_567_ = v___y_593_;
v___y_568_ = v___y_594_;
v___y_569_ = v___y_595_;
v___y_570_ = v___y_596_;
v___y_571_ = v___y_597_;
v___y_572_ = v___y_598_;
v___y_573_ = v___y_599_;
v___y_574_ = v___y_600_;
v_a_575_ = v_a_602_;
goto v___jp_564_;
}
else
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___y_601_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___y_601_);
v___y_578_ = v___y_591_;
v___y_579_ = v___y_592_;
v___y_580_ = v___y_593_;
v___y_581_ = v___y_594_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v___y_584_ = v___y_597_;
v___y_585_ = v___y_598_;
v___y_586_ = v___y_599_;
v___y_587_ = v___y_600_;
v_a_588_ = v_a_603_;
goto v___jp_577_;
}
}
v___jp_604_:
{
lean_object* v___x_616_; double v___x_617_; double v___x_618_; double v___x_619_; double v___x_620_; double v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_616_ = lean_io_mono_nanos_now();
v___x_617_ = lean_float_of_nat(v___y_608_);
v___x_618_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_619_ = lean_float_div(v___x_617_, v___x_618_);
v___x_620_ = lean_float_of_nat(v___x_616_);
v___x_621_ = lean_float_div(v___x_620_, v___x_618_);
v___x_622_ = lean_box_float(v___x_619_);
v___x_623_ = lean_box_float(v___x_621_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_a_615_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_607_);
v___x_626_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_607_, v___y_605_, v___y_609_, v___y_606_, v___y_611_, v___y_614_, v___y_612_, v___x_625_, v___y_613_, v___y_610_);
return v___x_626_;
}
v___jp_627_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v_a_638_);
v___y_605_ = v___y_628_;
v___y_606_ = v___y_629_;
v___y_607_ = v___y_630_;
v___y_608_ = v___y_631_;
v___y_609_ = v___y_632_;
v___y_610_ = v___y_633_;
v___y_611_ = v___y_634_;
v___y_612_ = v___y_635_;
v___y_613_ = v___y_636_;
v___y_614_ = v___y_637_;
v_a_615_ = v___x_639_;
goto v___jp_604_;
}
v___jp_640_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_a_651_);
v___y_605_ = v___y_641_;
v___y_606_ = v___y_642_;
v___y_607_ = v___y_643_;
v___y_608_ = v___y_644_;
v___y_609_ = v___y_645_;
v___y_610_ = v___y_646_;
v___y_611_ = v___y_647_;
v___y_612_ = v___y_648_;
v___y_613_ = v___y_649_;
v___y_614_ = v___y_650_;
v_a_615_ = v___x_652_;
goto v___jp_604_;
}
v___jp_653_:
{
if (lean_obj_tag(v___y_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___y_664_);
v___y_628_ = v___y_654_;
v___y_629_ = v___y_655_;
v___y_630_ = v___y_656_;
v___y_631_ = v___y_657_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_659_;
v___y_634_ = v___y_660_;
v___y_635_ = v___y_661_;
v___y_636_ = v___y_662_;
v___y_637_ = v___y_663_;
v_a_638_ = v_a_665_;
goto v___jp_627_;
}
else
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_a_666_);
lean_dec_ref(v___y_664_);
v___y_641_ = v___y_654_;
v___y_642_ = v___y_655_;
v___y_643_ = v___y_656_;
v___y_644_ = v___y_657_;
v___y_645_ = v___y_658_;
v___y_646_ = v___y_659_;
v___y_647_ = v___y_660_;
v___y_648_ = v___y_661_;
v___y_649_ = v___y_662_;
v___y_650_ = v___y_663_;
v_a_651_ = v_a_666_;
goto v___jp_640_;
}
}
v___jp_667_:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_673_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = l_Lean_trace_profiler_useHeartbeats;
v___x_684_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_670_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_io_mono_nanos_now();
v___x_686_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_676_, v___y_678_, v___y_673_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref(v___x_686_);
if (lean_obj_tag(v___y_679_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_val_687_ = lean_ctor_get(v___y_679_, 0);
lean_inc(v_val_687_);
lean_dec_ref(v___y_679_);
v___x_688_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_672_);
v___x_689_ = l_Lean_Name_mkStr2(v___y_672_, v___x_688_);
v___x_690_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_689_);
v___x_691_ = l_Lean_Name_append(v___x_690_, v___x_689_);
v___x_692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_680_, v___y_670_, v___x_691_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec(v___x_689_);
lean_dec(v_val_687_);
v___x_693_ = lean_box(0);
v___y_628_ = v___y_668_;
v___y_629_ = v___y_670_;
v___y_630_ = v___y_671_;
v___y_631_ = v___x_685_;
v___y_632_ = v___y_675_;
v___y_633_ = v___y_673_;
v___y_634_ = v___y_674_;
v___y_635_ = v___y_677_;
v___y_636_ = v___y_678_;
v___y_637_ = v_a_682_;
v_a_638_ = v___x_693_;
goto v___jp_627_;
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
lean_dec_ref(v___x_695_);
v___x_697_ = l_Lean_MessageData_ofFormat(v_a_696_);
v___x_698_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_689_, v___x_697_, v___y_678_, v___y_673_);
v___y_654_ = v___y_668_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___x_685_;
v___y_658_ = v___y_675_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
v___y_661_ = v___y_677_;
v___y_662_ = v___y_678_;
v___y_663_ = v_a_682_;
v___y_664_ = v___x_698_;
goto v___jp_653_;
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
lean_inc(v___y_669_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_669_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___y_641_ = v___y_668_;
v___y_642_ = v___y_670_;
v___y_643_ = v___y_671_;
v___y_644_ = v___x_685_;
v___y_645_ = v___y_675_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_674_;
v___y_648_ = v___y_677_;
v___y_649_ = v___y_678_;
v___y_650_ = v_a_682_;
v_a_651_ = v___x_707_;
goto v___jp_640_;
}
}
}
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v___y_679_);
v___x_710_ = lean_box(0);
v___y_628_ = v___y_668_;
v___y_629_ = v___y_670_;
v___y_630_ = v___y_671_;
v___y_631_ = v___x_685_;
v___y_632_ = v___y_675_;
v___y_633_ = v___y_673_;
v___y_634_ = v___y_674_;
v___y_635_ = v___y_677_;
v___y_636_ = v___y_678_;
v___y_637_ = v_a_682_;
v_a_638_ = v___x_710_;
goto v___jp_627_;
}
}
else
{
lean_dec(v___y_679_);
v___y_654_ = v___y_668_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___x_685_;
v___y_658_ = v___y_675_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
v___y_661_ = v___y_677_;
v___y_662_ = v___y_678_;
v___y_663_ = v_a_682_;
v___y_664_ = v___x_686_;
goto v___jp_653_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_io_get_num_heartbeats();
v___x_712_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_676_, v___y_678_, v___y_673_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_dec_ref(v___x_712_);
if (lean_obj_tag(v___y_679_) == 1)
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_val_713_ = lean_ctor_get(v___y_679_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v___y_679_);
v___x_714_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_672_);
v___x_715_ = l_Lean_Name_mkStr2(v___y_672_, v___x_714_);
v___x_716_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_715_);
v___x_717_ = l_Lean_Name_append(v___x_716_, v___x_715_);
v___x_718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_680_, v___y_670_, v___x_717_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec(v___x_715_);
lean_dec(v_val_713_);
v___x_719_ = lean_box(0);
v___y_565_ = v___y_668_;
v___y_566_ = v___y_670_;
v___y_567_ = v___y_671_;
v___y_568_ = v___y_675_;
v___y_569_ = v___y_673_;
v___y_570_ = v___y_674_;
v___y_571_ = v___x_711_;
v___y_572_ = v___y_677_;
v___y_573_ = v___y_678_;
v___y_574_ = v_a_682_;
v_a_575_ = v___x_719_;
goto v___jp_564_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Lean_Elab_InfoTree_format(v_val_713_, v___x_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Lean_MessageData_ofFormat(v_a_722_);
v___x_724_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_715_, v___x_723_, v___y_678_, v___y_673_);
v___y_591_ = v___y_668_;
v___y_592_ = v___y_670_;
v___y_593_ = v___y_671_;
v___y_594_ = v___y_675_;
v___y_595_ = v___y_673_;
v___y_596_ = v___y_674_;
v___y_597_ = v___x_711_;
v___y_598_ = v___y_677_;
v___y_599_ = v___y_678_;
v___y_600_ = v_a_682_;
v___y_601_ = v___x_724_;
goto v___jp_590_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
lean_dec(v___x_715_);
v_a_725_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_735_ == 0)
{
v___x_727_ = v___x_721_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_io_error_to_string(v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 3);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_734_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_MessageData_ofFormat(v___x_731_);
lean_inc(v___y_669_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_669_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___y_578_ = v___y_668_;
v___y_579_ = v___y_670_;
v___y_580_ = v___y_671_;
v___y_581_ = v___y_675_;
v___y_582_ = v___y_673_;
v___y_583_ = v___y_674_;
v___y_584_ = v___x_711_;
v___y_585_ = v___y_677_;
v___y_586_ = v___y_678_;
v___y_587_ = v_a_682_;
v_a_588_ = v___x_733_;
goto v___jp_577_;
}
}
}
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v___y_679_);
v___x_736_ = lean_box(0);
v___y_565_ = v___y_668_;
v___y_566_ = v___y_670_;
v___y_567_ = v___y_671_;
v___y_568_ = v___y_675_;
v___y_569_ = v___y_673_;
v___y_570_ = v___y_674_;
v___y_571_ = v___x_711_;
v___y_572_ = v___y_677_;
v___y_573_ = v___y_678_;
v___y_574_ = v_a_682_;
v_a_575_ = v___x_736_;
goto v___jp_564_;
}
}
else
{
lean_dec(v___y_679_);
v___y_591_ = v___y_668_;
v___y_592_ = v___y_670_;
v___y_593_ = v___y_671_;
v___y_594_ = v___y_675_;
v___y_595_ = v___y_673_;
v___y_596_ = v___y_674_;
v___y_597_ = v___x_711_;
v___y_598_ = v___y_677_;
v___y_599_ = v___y_678_;
v___y_600_ = v_a_682_;
v___y_601_ = v___x_712_;
goto v___jp_590_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___y_679_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
v_a_737_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_681_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_681_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
v_resetjp_747_:
{
lean_object* v_desc_750_; lean_object* v_diagnostics_751_; lean_object* v_infoTree_x3f_752_; lean_object* v_desc_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___x_850_; 
v_desc_750_ = lean_ctor_get(v_element_745_, 0);
lean_inc_ref(v_desc_750_);
v_diagnostics_751_ = lean_ctor_get(v_element_745_, 1);
lean_inc_ref(v_diagnostics_751_);
v_infoTree_x3f_752_ = lean_ctor_get(v_element_745_, 2);
lean_inc(v_infoTree_x3f_752_);
lean_dec_ref(v_element_745_);
v___x_850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_850_, 0, v_desc_750_);
switch(lean_obj_tag(v_range_x3f_539_))
{
case 0:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v_desc_754_ = v___x_852_;
v___y_755_ = v_a_541_;
v___y_756_ = v_a_542_;
goto v___jp_753_;
}
case 1:
{
lean_object* v_range_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_911_; 
v_range_853_ = lean_ctor_get(v_range_x3f_539_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_range_x3f_539_);
if (v_isSharedCheck_911_ == 0)
{
v___x_855_ = v_range_x3f_539_;
v_isShared_856_ = v_isSharedCheck_911_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_range_853_);
lean_dec(v_range_x3f_539_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_911_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fileMap_857_; lean_object* v_start_858_; lean_object* v_stop_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_910_; 
v_fileMap_857_ = lean_ctor_get(v_a_541_, 1);
v_start_858_ = lean_ctor_get(v_range_853_, 0);
v_stop_859_ = lean_ctor_get(v_range_853_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_range_853_);
if (v_isSharedCheck_910_ == 0)
{
v___x_861_ = v_range_853_;
v_isShared_862_ = v_isSharedCheck_910_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_stop_859_);
lean_inc(v_start_858_);
lean_dec(v_range_853_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_910_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v_line_864_; lean_object* v_column_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_909_; 
lean_inc_ref(v_fileMap_857_);
v___x_863_ = l_Lean_FileMap_toPosition(v_fileMap_857_, v_start_858_);
lean_dec(v_start_858_);
v_line_864_ = lean_ctor_get(v___x_863_, 0);
v_column_865_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_909_ == 0)
{
v___x_867_ = v___x_863_;
v_isShared_868_ = v_isSharedCheck_909_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_column_865_);
lean_inc(v_line_864_);
lean_dec(v___x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_909_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v_line_870_; lean_object* v_column_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_908_; 
lean_inc_ref(v_fileMap_857_);
v___x_869_ = l_Lean_FileMap_toPosition(v_fileMap_857_, v_stop_859_);
lean_dec(v_stop_859_);
v_line_870_ = lean_ctor_get(v___x_869_, 0);
v_column_871_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_908_ == 0)
{
v___x_873_ = v___x_869_;
v_isShared_874_ = v_isSharedCheck_908_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_column_871_);
lean_inc(v_line_870_);
lean_dec(v___x_869_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_908_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_876_ = l_Nat_reprFast(v_line_864_);
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 3);
lean_ctor_set(v___x_855_, 0, v___x_876_);
v___x_878_ = v___x_855_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_907_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 5);
lean_ctor_set(v___x_873_, 1, v___x_878_);
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_906_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 5);
lean_ctor_set(v___x_867_, 1, v___x_881_);
lean_ctor_set(v___x_867_, 0, v___x_880_);
v___x_883_ = v___x_867_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_905_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = l_Nat_reprFast(v_column_865_);
v___x_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 5);
lean_ctor_set(v___x_861_, 1, v___x_885_);
lean_ctor_set(v___x_861_, 0, v___x_883_);
v___x_887_ = v___x_861_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_904_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Nat_reprFast(v_line_870_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_875_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_881_);
v___x_896_ = l_Nat_reprFast(v_column_871_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_888_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_891_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__22));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_850_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v_desc_754_ = v___x_903_;
v___y_755_ = v_a_541_;
v___y_756_ = v_a_542_;
goto v___jp_753_;
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
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__24));
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_850_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v_desc_754_ = v___x_913_;
v___y_755_ = v_a_541_;
v___y_756_ = v_a_542_;
goto v___jp_753_;
}
}
v___jp_753_:
{
lean_object* v_msgLog_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_848_; 
v_msgLog_757_ = lean_ctor_get(v_diagnostics_751_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_diagnostics_751_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_diagnostics_751_, 1);
lean_dec(v_unused_849_);
v___x_759_ = v_diagnostics_751_;
v_isShared_760_ = v_isSharedCheck_848_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_msgLog_757_);
lean_dec(v_diagnostics_751_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_848_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_MessageLog_toList(v_msgLog_757_);
lean_dec_ref(v_msgLog_757_);
v___x_762_ = lean_box(0);
v___x_763_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_761_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_options_764_; lean_object* v_a_765_; lean_object* v_ref_766_; lean_object* v_inheritedTraceOptions_767_; uint8_t v_hasTrace_768_; lean_object* v___x_769_; 
v_options_764_ = lean_ctor_get(v___y_755_, 2);
v_a_765_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_763_);
v_ref_766_ = lean_ctor_get(v___y_755_, 5);
v_inheritedTraceOptions_767_ = lean_ctor_get(v___y_755_, 13);
v_hasTrace_768_ = lean_ctor_get_uint8(v_options_764_, sizeof(void*)*1);
v___x_769_ = lean_array_to_list(v_children_746_);
if (v_hasTrace_768_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_a_765_);
lean_del_object(v___x_759_);
lean_dec(v_desc_754_);
lean_del_object(v___x_748_);
v___x_770_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_769_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_770_, 0);
lean_dec(v_unused_783_);
v___x_772_ = v___x_770_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_dec(v___x_770_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
if (lean_obj_tag(v_infoTree_x3f_752_) == 1)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec_ref(v_infoTree_x3f_752_);
v___x_774_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_774_);
v___x_776_ = v___x_772_;
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
else
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_infoTree_x3f_752_);
v___x_778_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_778_);
v___x_780_ = v___x_772_;
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
}
}
else
{
lean_dec(v_infoTree_x3f_752_);
return v___x_770_;
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_785_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_786_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_785_, v_a_765_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 5);
lean_ctor_set(v___x_759_, 1, v___x_786_);
lean_ctor_set(v___x_759_, 0, v_desc_754_);
v___x_788_ = v___x_759_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_desc_754_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_839_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___f_789_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_789_, 0, v___x_788_);
v___x_790_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_791_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_792_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_767_, v_options_764_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = l_Lean_trace_profiler;
v___x_795_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_764_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec_ref(v___f_789_);
v___x_796_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_769_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_837_; 
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_838_);
v___x_798_ = v___x_796_;
v_isShared_799_ = v_isSharedCheck_837_;
goto v_resetjp_797_;
}
else
{
lean_dec(v___x_796_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_837_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_infoTree_x3f_752_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_832_; 
v_val_800_ = lean_ctor_get(v_infoTree_x3f_752_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_infoTree_x3f_752_);
if (v_isSharedCheck_832_ == 0)
{
v___x_802_ = v_infoTree_x3f_752_;
v_isShared_803_ = v_isSharedCheck_832_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v_infoTree_x3f_752_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_832_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_805_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_767_, v_options_764_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_del_object(v___x_802_);
lean_dec(v_val_800_);
lean_del_object(v___x_748_);
v___x_807_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_807_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_del_object(v___x_798_);
v___x_811_ = lean_box(0);
v___x_812_ = l_Lean_Elab_InfoTree_format(v_val_800_, v___x_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_del_object(v___x_802_);
lean_del_object(v___x_748_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = l_Lean_MessageData_ofFormat(v_a_813_);
v___x_815_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_804_, v___x_814_, v___y_755_, v___y_756_);
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_831_; 
v_a_816_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_831_ == 0)
{
v___x_818_ = v___x_812_;
v_isShared_819_ = v_isSharedCheck_831_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_831_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_io_error_to_string(v_a_816_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 3);
lean_ctor_set(v___x_802_, 0, v___x_820_);
v___x_822_ = v___x_802_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_830_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_MessageData_ofFormat(v___x_822_);
lean_inc(v_ref_766_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_823_);
lean_ctor_set(v___x_748_, 0, v_ref_766_);
v___x_825_ = v___x_748_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_ref_766_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_825_);
v___x_827_ = v___x_818_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
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
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_infoTree_x3f_752_);
lean_del_object(v___x_748_);
v___x_833_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_833_);
v___x_835_ = v___x_798_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_752_);
lean_del_object(v___x_748_);
return v___x_796_;
}
}
else
{
lean_del_object(v___x_748_);
v___y_668_ = v_hasTrace_768_;
v___y_669_ = v_ref_766_;
v___y_670_ = v_options_764_;
v___y_671_ = v___x_790_;
v___y_672_ = v___x_784_;
v___y_673_ = v___y_756_;
v___y_674_ = v___x_793_;
v___y_675_ = v___x_791_;
v___y_676_ = v___x_769_;
v___y_677_ = v___f_789_;
v___y_678_ = v___y_755_;
v___y_679_ = v_infoTree_x3f_752_;
v___y_680_ = v_inheritedTraceOptions_767_;
goto v___jp_667_;
}
}
else
{
lean_del_object(v___x_748_);
v___y_668_ = v_hasTrace_768_;
v___y_669_ = v_ref_766_;
v___y_670_ = v_options_764_;
v___y_671_ = v___x_790_;
v___y_672_ = v___x_784_;
v___y_673_ = v___y_756_;
v___y_674_ = v___x_793_;
v___y_675_ = v___x_791_;
v___y_676_ = v___x_769_;
v___y_677_ = v___f_789_;
v___y_678_ = v___y_755_;
v___y_679_ = v_infoTree_x3f_752_;
v___y_680_ = v_inheritedTraceOptions_767_;
goto v___jp_667_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_759_);
lean_dec(v_desc_754_);
lean_dec(v_infoTree_x3f_752_);
lean_del_object(v___x_748_);
lean_dec_ref(v_children_746_);
v_a_840_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_763_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_763_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
if (lean_obj_tag(v_as_915_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v_reportingRange_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_head_921_ = lean_ctor_get(v_as_915_, 0);
lean_inc(v_head_921_);
v_tail_922_ = lean_ctor_get(v_as_915_, 1);
lean_inc(v_tail_922_);
lean_dec_ref(v_as_915_);
v_reportingRange_923_ = lean_ctor_get(v_head_921_, 1);
lean_inc(v_reportingRange_923_);
v___x_924_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_921_);
v___x_925_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_923_, v___x_924_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref(v___x_925_);
v_as_915_ = v_tail_922_;
goto _start;
}
else
{
lean_dec(v_tail_922_);
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_932_, lean_object* v_s_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_932_, v_s_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_938_, v_x_939_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_944_, v_x_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_00_u03b1_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___redArg(v_x_951_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_00_u03b1_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_00_u03b1_956_, v_x_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_box(2);
v___x_967_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_966_, v_s_962_, v_a_963_, v_a_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Language_SnapshotTree_trace(v_s_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_972_;
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

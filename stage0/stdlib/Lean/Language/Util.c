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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* lean_io_get_num_heartbeats();
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 108, 214, 181, 226, 69, 54, 12)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snapshotTree"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(11, 136, 72, 78, 187, 126, 217, 153)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "\n• "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "<range inherited> "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__12_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__14_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__16_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18_value;
static const lean_string_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<no range> "};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value;
static const lean_ctor_object l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19_value)}};
static const lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20 = (const lean_object*)&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v_cls_21_, v___y_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_30_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(32u);
v___x_32_ = lean_mk_empty_array_with_capacity(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((size_t)5ULL);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_unsigned_to_nat(32u);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_38_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__0);
v___x_39_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_35_);
lean_ctor_set(v___x_39_, 3, v___x_35_);
lean_ctor_set_usize(v___x_39_, 4, v___x_34_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v_traceState_43_; lean_object* v_traces_44_; lean_object* v___x_45_; lean_object* v_traceState_46_; lean_object* v_env_47_; lean_object* v_nextMacroScope_48_; lean_object* v_ngen_49_; lean_object* v_auxDeclNGen_50_; lean_object* v_cache_51_; lean_object* v_messages_52_; lean_object* v_infoState_53_; lean_object* v_snapshotTasks_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_73_; 
v___x_42_ = lean_st_ref_get(v___y_40_);
v_traceState_43_ = lean_ctor_get(v___x_42_, 4);
lean_inc_ref(v_traceState_43_);
lean_dec(v___x_42_);
v_traces_44_ = lean_ctor_get(v_traceState_43_, 0);
lean_inc_ref(v_traces_44_);
lean_dec_ref(v_traceState_43_);
v___x_45_ = lean_st_ref_take(v___y_40_);
v_traceState_46_ = lean_ctor_get(v___x_45_, 4);
v_env_47_ = lean_ctor_get(v___x_45_, 0);
v_nextMacroScope_48_ = lean_ctor_get(v___x_45_, 1);
v_ngen_49_ = lean_ctor_get(v___x_45_, 2);
v_auxDeclNGen_50_ = lean_ctor_get(v___x_45_, 3);
v_cache_51_ = lean_ctor_get(v___x_45_, 5);
v_messages_52_ = lean_ctor_get(v___x_45_, 6);
v_infoState_53_ = lean_ctor_get(v___x_45_, 7);
v_snapshotTasks_54_ = lean_ctor_get(v___x_45_, 8);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_73_ == 0)
{
v___x_56_ = v___x_45_;
v_isShared_57_ = v_isSharedCheck_73_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_snapshotTasks_54_);
lean_inc(v_infoState_53_);
lean_inc(v_messages_52_);
lean_inc(v_cache_51_);
lean_inc(v_traceState_46_);
lean_inc(v_auxDeclNGen_50_);
lean_inc(v_ngen_49_);
lean_inc(v_nextMacroScope_48_);
lean_inc(v_env_47_);
lean_dec(v___x_45_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_73_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
uint64_t v_tid_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_71_; 
v_tid_58_ = lean_ctor_get_uint64(v_traceState_46_, sizeof(void*)*1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_traceState_46_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_traceState_46_, 0);
lean_dec(v_unused_72_);
v___x_60_ = v_traceState_46_;
v_isShared_61_ = v_isSharedCheck_71_;
goto v_resetjp_59_;
}
else
{
lean_dec(v_traceState_46_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_71_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___closed__1);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_62_);
v___x_64_ = v___x_60_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_62_);
lean_ctor_set_uint64(v_reuseFailAlloc_70_, sizeof(void*)*1, v_tid_58_);
v___x_64_ = v_reuseFailAlloc_70_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_64_);
v___x_66_ = v___x_56_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_env_47_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_nextMacroScope_48_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_ngen_49_);
lean_ctor_set(v_reuseFailAlloc_69_, 3, v_auxDeclNGen_50_);
lean_ctor_set(v_reuseFailAlloc_69_, 4, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_69_, 5, v_cache_51_);
lean_ctor_set(v_reuseFailAlloc_69_, 6, v_messages_52_);
lean_ctor_set(v_reuseFailAlloc_69_, 7, v_infoState_53_);
lean_ctor_set(v_reuseFailAlloc_69_, 8, v_snapshotTasks_54_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_st_ref_set(v___y_40_, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v_traces_44_);
return v___x_68_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg___boxed(lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(v___y_74_);
lean_dec(v___y_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(v___y_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_opts_85_, lean_object* v_opt_86_){
_start:
{
lean_object* v_name_87_; lean_object* v_defValue_88_; lean_object* v_map_89_; lean_object* v___x_90_; 
v_name_87_ = lean_ctor_get(v_opt_86_, 0);
v_defValue_88_ = lean_ctor_get(v_opt_86_, 1);
v_map_89_ = lean_ctor_get(v_opts_85_, 0);
v___x_90_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_89_, v_name_87_);
if (lean_obj_tag(v___x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = lean_unbox(v_defValue_88_);
return v___x_91_;
}
else
{
lean_object* v_val_92_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_92_);
lean_dec_ref(v___x_90_);
if (lean_obj_tag(v_val_92_) == 1)
{
uint8_t v_v_93_; 
v_v_93_ = lean_ctor_get_uint8(v_val_92_, 0);
lean_dec_ref(v_val_92_);
return v_v_93_;
}
else
{
uint8_t v___x_94_; 
lean_dec(v_val_92_);
v___x_94_ = lean_unbox(v_defValue_88_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_opts_95_, v_opt_96_);
lean_dec_ref(v_opt_96_);
lean_dec_ref(v_opts_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object* v___x_99_, lean_object* v_x_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = l_Lean_MessageData_ofFormat(v___x_99_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object* v___x_106_, lean_object* v_x_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(v___x_106_, v_x_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec_ref(v_x_107_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(lean_object* v_pre_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_dec(v_pre_112_);
return v_x_113_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v_head_115_ = lean_ctor_get(v_x_114_, 0);
v_tail_116_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_126_ == 0)
{
v___x_118_ = v_x_114_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_head_115_);
lean_dec(v_x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
lean_inc(v_pre_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 5);
lean_ctor_set(v___x_118_, 1, v_pre_112_);
lean_ctor_set(v___x_118_, 0, v_x_113_);
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_x_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_pre_112_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_122_, 0, v_head_115_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v_x_113_ = v___x_123_;
v_x_114_ = v_tail_116_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object* v_pre_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_129_; 
lean_dec(v_pre_127_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_140_; 
v_head_130_ = lean_ctor_get(v_x_128_, 0);
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_128_);
if (v_isSharedCheck_140_ == 0)
{
v___x_133_ = v_x_128_;
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_tail_131_);
lean_inc(v_head_130_);
lean_dec(v_x_128_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v_head_130_);
lean_inc(v_pre_127_);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 5);
lean_ctor_set(v___x_133_, 1, v___x_135_);
lean_ctor_set(v___x_133_, 0, v_pre_127_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_pre_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_139_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; 
v___x_138_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(v_pre_127_, v___x_137_, v_tail_131_);
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_List_reverse___redArg(v_x_142_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_157_; 
v_head_146_ = lean_ctor_get(v_x_141_, 0);
v_tail_147_ = lean_ctor_get(v_x_141_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_149_ = v_x_141_;
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_head_146_);
lean_dec(v_x_141_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = 0;
v___x_152_ = l_Lean_Message_toString(v_head_146_, v___x_151_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_x_142_);
lean_ctor_set(v___x_149_, 0, v___x_152_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_x_142_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
v_x_141_ = v_tail_147_;
v_x_142_ = v___x_154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_158_, v_x_159_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__0);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_ctor_set(v___x_167_, 2, v___x_166_);
lean_ctor_set(v___x_167_, 3, v___x_165_);
lean_ctor_set(v___x_167_, 4, v___x_165_);
lean_ctor_set(v___x_167_, 5, v___x_165_);
lean_ctor_set(v___x_167_, 6, v___x_165_);
lean_ctor_set(v___x_167_, 7, v___x_165_);
lean_ctor_set(v___x_167_, 8, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4(void){
_start:
{
size_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__3);
v___x_176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set_usize(v___x_176_, 4, v___x_171_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_box(1);
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__4);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__1);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(lean_object* v_msgData_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_env_186_; lean_object* v_options_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_185_ = lean_st_ref_get(v___y_183_);
v_env_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc_ref(v_env_186_);
lean_dec(v___x_185_);
v_options_187_ = lean_ctor_get(v___y_182_, 2);
v___x_188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__2);
v___x_189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___closed__5);
lean_inc_ref(v_options_187_);
v___x_190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_190_, 0, v_env_186_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
lean_ctor_set(v___x_190_, 3, v_options_187_);
v___x_191_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_msgData_181_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3___boxed(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(v_msgData_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_197_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_198_; double v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_float_of_nat(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_cls_203_, lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_254_; 
v_ref_208_ = lean_ctor_get(v___y_205_, 5);
v___x_209_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(v_msg_204_, v___y_205_, v___y_206_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_254_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_254_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_254_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_traceState_215_; lean_object* v_env_216_; lean_object* v_nextMacroScope_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_cache_220_; lean_object* v_messages_221_; lean_object* v_infoState_222_; lean_object* v_snapshotTasks_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_253_; 
v___x_214_ = lean_st_ref_take(v___y_206_);
v_traceState_215_ = lean_ctor_get(v___x_214_, 4);
v_env_216_ = lean_ctor_get(v___x_214_, 0);
v_nextMacroScope_217_ = lean_ctor_get(v___x_214_, 1);
v_ngen_218_ = lean_ctor_get(v___x_214_, 2);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_214_, 3);
v_cache_220_ = lean_ctor_get(v___x_214_, 5);
v_messages_221_ = lean_ctor_get(v___x_214_, 6);
v_infoState_222_ = lean_ctor_get(v___x_214_, 7);
v_snapshotTasks_223_ = lean_ctor_get(v___x_214_, 8);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_253_ == 0)
{
v___x_225_ = v___x_214_;
v_isShared_226_ = v_isSharedCheck_253_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snapshotTasks_223_);
lean_inc(v_infoState_222_);
lean_inc(v_messages_221_);
lean_inc(v_cache_220_);
lean_inc(v_traceState_215_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_env_216_);
lean_dec(v___x_214_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_253_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint64_t v_tid_227_; lean_object* v_traces_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_252_; 
v_tid_227_ = lean_ctor_get_uint64(v_traceState_215_, sizeof(void*)*1);
v_traces_228_ = lean_ctor_get(v_traceState_215_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_traceState_215_);
if (v_isSharedCheck_252_ == 0)
{
v___x_230_ = v_traceState_215_;
v_isShared_231_ = v_isSharedCheck_252_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_traces_228_);
lean_dec(v_traceState_215_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_252_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; double v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0);
v___x_234_ = 0;
v___x_235_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1));
v___x_236_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_236_, 0, v_cls_203_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3, v___x_233_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3 + 8, v___x_233_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 16, v___x_234_);
v___x_237_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__2));
v___x_238_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v_a_210_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_inc(v_ref_208_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_208_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_Lean_PersistentArray_push___redArg(v_traces_228_, v___x_239_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_240_);
v___x_242_ = v___x_230_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_240_);
lean_ctor_set_uint64(v_reuseFailAlloc_251_, sizeof(void*)*1, v_tid_227_);
v___x_242_ = v_reuseFailAlloc_251_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 4, v___x_242_);
v___x_244_ = v___x_225_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_env_216_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v_messages_221_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v_snapshotTasks_223_);
v___x_244_ = v_reuseFailAlloc_250_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_245_ = lean_st_ref_set(v___y_206_, v___x_244_);
v___x_246_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_246_);
v___x_248_ = v___x_212_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___boxed(lean_object* v_cls_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v_cls_255_, v_msg_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(lean_object* v_opts_261_, lean_object* v_opt_262_){
_start:
{
lean_object* v_name_263_; lean_object* v_defValue_264_; lean_object* v_map_265_; lean_object* v___x_266_; 
v_name_263_ = lean_ctor_get(v_opt_262_, 0);
v_defValue_264_ = lean_ctor_get(v_opt_262_, 1);
v_map_265_ = lean_ctor_get(v_opts_261_, 0);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_265_, v_name_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_inc(v_defValue_264_);
return v_defValue_264_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_267_);
lean_dec_ref(v___x_266_);
if (lean_obj_tag(v_val_267_) == 3)
{
lean_object* v_v_268_; 
v_v_268_ = lean_ctor_get(v_val_267_, 0);
lean_inc(v_v_268_);
lean_dec_ref(v_val_267_);
return v_v_268_;
}
else
{
lean_dec(v_val_267_);
lean_inc(v_defValue_264_);
return v_defValue_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12___boxed(lean_object* v_opts_269_, lean_object* v_opt_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(v_opts_269_, v_opt_270_);
lean_dec_ref(v_opt_270_);
lean_dec_ref(v_opts_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11(size_t v_sz_272_, size_t v_i_273_, lean_object* v_bs_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_usize_dec_lt(v_i_273_, v_sz_272_);
if (v___x_275_ == 0)
{
return v_bs_274_;
}
else
{
lean_object* v_v_276_; lean_object* v_msg_277_; lean_object* v___x_278_; lean_object* v_bs_x27_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v_v_276_ = lean_array_uget_borrowed(v_bs_274_, v_i_273_);
v_msg_277_ = lean_ctor_get(v_v_276_, 1);
lean_inc_ref(v_msg_277_);
v___x_278_ = lean_unsigned_to_nat(0u);
v_bs_x27_279_ = lean_array_uset(v_bs_274_, v_i_273_, v___x_278_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_273_, v___x_280_);
v___x_282_ = lean_array_uset(v_bs_x27_279_, v_i_273_, v_msg_277_);
v_i_273_ = v___x_281_;
v_bs_274_ = v___x_282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11___boxed(lean_object* v_sz_284_, lean_object* v_i_285_, lean_object* v_bs_286_){
_start:
{
size_t v_sz_boxed_287_; size_t v_i_boxed_288_; lean_object* v_res_289_; 
v_sz_boxed_287_ = lean_unbox_usize(v_sz_284_);
lean_dec(v_sz_284_);
v_i_boxed_288_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11(v_sz_boxed_287_, v_i_boxed_288_, v_bs_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(lean_object* v_oldTraces_290_, lean_object* v_data_291_, lean_object* v_ref_292_, lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_fileName_297_; lean_object* v_fileMap_298_; lean_object* v_options_299_; lean_object* v_currRecDepth_300_; lean_object* v_maxRecDepth_301_; lean_object* v_ref_302_; lean_object* v_currNamespace_303_; lean_object* v_openDecls_304_; lean_object* v_initHeartbeats_305_; lean_object* v_maxHeartbeats_306_; lean_object* v_quotContext_307_; lean_object* v_currMacroScope_308_; uint8_t v_diag_309_; lean_object* v_cancelTk_x3f_310_; uint8_t v_suppressElabErrors_311_; lean_object* v_inheritedTraceOptions_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_367_; 
v_fileName_297_ = lean_ctor_get(v___y_294_, 0);
v_fileMap_298_ = lean_ctor_get(v___y_294_, 1);
v_options_299_ = lean_ctor_get(v___y_294_, 2);
v_currRecDepth_300_ = lean_ctor_get(v___y_294_, 3);
v_maxRecDepth_301_ = lean_ctor_get(v___y_294_, 4);
v_ref_302_ = lean_ctor_get(v___y_294_, 5);
v_currNamespace_303_ = lean_ctor_get(v___y_294_, 6);
v_openDecls_304_ = lean_ctor_get(v___y_294_, 7);
v_initHeartbeats_305_ = lean_ctor_get(v___y_294_, 8);
v_maxHeartbeats_306_ = lean_ctor_get(v___y_294_, 9);
v_quotContext_307_ = lean_ctor_get(v___y_294_, 10);
v_currMacroScope_308_ = lean_ctor_get(v___y_294_, 11);
v_diag_309_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*14);
v_cancelTk_x3f_310_ = lean_ctor_get(v___y_294_, 12);
v_suppressElabErrors_311_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_312_ = lean_ctor_get(v___y_294_, 13);
v_isSharedCheck_367_ = !lean_is_exclusive(v___y_294_);
if (v_isSharedCheck_367_ == 0)
{
v___x_314_ = v___y_294_;
v_isShared_315_ = v_isSharedCheck_367_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_inheritedTraceOptions_312_);
lean_inc(v_cancelTk_x3f_310_);
lean_inc(v_currMacroScope_308_);
lean_inc(v_quotContext_307_);
lean_inc(v_maxHeartbeats_306_);
lean_inc(v_initHeartbeats_305_);
lean_inc(v_openDecls_304_);
lean_inc(v_currNamespace_303_);
lean_inc(v_ref_302_);
lean_inc(v_maxRecDepth_301_);
lean_inc(v_currRecDepth_300_);
lean_inc(v_options_299_);
lean_inc(v_fileMap_298_);
lean_inc(v_fileName_297_);
lean_dec(v___y_294_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_367_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v_traceState_317_; lean_object* v_traces_318_; lean_object* v_ref_319_; lean_object* v___x_321_; 
v___x_316_ = lean_st_ref_get(v___y_295_);
v_traceState_317_ = lean_ctor_get(v___x_316_, 4);
lean_inc_ref(v_traceState_317_);
lean_dec(v___x_316_);
v_traces_318_ = lean_ctor_get(v_traceState_317_, 0);
lean_inc_ref(v_traces_318_);
lean_dec_ref(v_traceState_317_);
v_ref_319_ = l_Lean_replaceRef(v_ref_292_, v_ref_302_);
lean_dec(v_ref_302_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 5, v_ref_319_);
v___x_321_ = v___x_314_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fileName_297_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_fileMap_298_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_options_299_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_currRecDepth_300_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_maxRecDepth_301_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_ref_319_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_currNamespace_303_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_openDecls_304_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v_initHeartbeats_305_);
lean_ctor_set(v_reuseFailAlloc_366_, 9, v_maxHeartbeats_306_);
lean_ctor_set(v_reuseFailAlloc_366_, 10, v_quotContext_307_);
lean_ctor_set(v_reuseFailAlloc_366_, 11, v_currMacroScope_308_);
lean_ctor_set(v_reuseFailAlloc_366_, 12, v_cancelTk_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_366_, 13, v_inheritedTraceOptions_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_366_, sizeof(void*)*14, v_diag_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_366_, sizeof(void*)*14 + 1, v_suppressElabErrors_311_);
v___x_321_ = v_reuseFailAlloc_366_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; size_t v_sz_323_; size_t v___x_324_; lean_object* v___x_325_; lean_object* v_msg_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_365_; 
v___x_322_ = l_Lean_PersistentArray_toArray___redArg(v_traces_318_);
lean_dec_ref(v_traces_318_);
v_sz_323_ = lean_array_size(v___x_322_);
v___x_324_ = ((size_t)0ULL);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11(v_sz_323_, v___x_324_, v___x_322_);
v_msg_326_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_326_, 0, v_data_291_);
lean_ctor_set(v_msg_326_, 1, v_msg_293_);
lean_ctor_set(v_msg_326_, 2, v___x_325_);
v___x_327_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(v_msg_326_, v___x_321_, v___y_295_);
lean_dec_ref(v___x_321_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_365_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_365_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_365_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_traceState_333_; lean_object* v_env_334_; lean_object* v_nextMacroScope_335_; lean_object* v_ngen_336_; lean_object* v_auxDeclNGen_337_; lean_object* v_cache_338_; lean_object* v_messages_339_; lean_object* v_infoState_340_; lean_object* v_snapshotTasks_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_364_; 
v___x_332_ = lean_st_ref_take(v___y_295_);
v_traceState_333_ = lean_ctor_get(v___x_332_, 4);
v_env_334_ = lean_ctor_get(v___x_332_, 0);
v_nextMacroScope_335_ = lean_ctor_get(v___x_332_, 1);
v_ngen_336_ = lean_ctor_get(v___x_332_, 2);
v_auxDeclNGen_337_ = lean_ctor_get(v___x_332_, 3);
v_cache_338_ = lean_ctor_get(v___x_332_, 5);
v_messages_339_ = lean_ctor_get(v___x_332_, 6);
v_infoState_340_ = lean_ctor_get(v___x_332_, 7);
v_snapshotTasks_341_ = lean_ctor_get(v___x_332_, 8);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_364_ == 0)
{
v___x_343_ = v___x_332_;
v_isShared_344_ = v_isSharedCheck_364_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snapshotTasks_341_);
lean_inc(v_infoState_340_);
lean_inc(v_messages_339_);
lean_inc(v_cache_338_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_337_);
lean_inc(v_ngen_336_);
lean_inc(v_nextMacroScope_335_);
lean_inc(v_env_334_);
lean_dec(v___x_332_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_364_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint64_t v_tid_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_362_; 
v_tid_345_ = lean_ctor_get_uint64(v_traceState_333_, sizeof(void*)*1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_traceState_333_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_traceState_333_, 0);
lean_dec(v_unused_363_);
v___x_347_ = v_traceState_333_;
v_isShared_348_ = v_isSharedCheck_362_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_traceState_333_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_362_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_ref_292_);
lean_ctor_set(v___x_349_, 1, v_a_328_);
v___x_350_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_290_, v___x_349_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_350_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_350_);
lean_ctor_set_uint64(v_reuseFailAlloc_361_, sizeof(void*)*1, v_tid_345_);
v___x_352_ = v_reuseFailAlloc_361_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 4, v___x_352_);
v___x_354_ = v___x_343_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_env_334_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_nextMacroScope_335_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_ngen_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_auxDeclNGen_337_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_360_, 5, v_cache_338_);
lean_ctor_set(v_reuseFailAlloc_360_, 6, v_messages_339_);
lean_ctor_set(v_reuseFailAlloc_360_, 7, v_infoState_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 8, v_snapshotTasks_341_);
v___x_354_ = v_reuseFailAlloc_360_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_355_ = lean_st_ref_set(v___y_295_, v___x_354_);
v___x_356_ = lean_box(0);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_356_);
v___x_358_ = v___x_330_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10___boxed(lean_object* v_oldTraces_368_, lean_object* v_data_369_, lean_object* v_ref_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(v_oldTraces_368_, v_data_369_, v_ref_370_, v_msg_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(lean_object* v_e_376_){
_start:
{
if (lean_obj_tag(v_e_376_) == 0)
{
uint8_t v___x_377_; 
v___x_377_ = 2;
return v___x_377_;
}
else
{
uint8_t v___x_378_; 
v___x_378_ = 0;
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9___boxed(lean_object* v_e_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(v_e_379_);
lean_dec_ref(v_e_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(lean_object* v_x_382_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v_x_382_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_x_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 1);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v_x_382_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v_x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 0);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg___boxed(lean_object* v_x_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_x_400_);
return v_res_402_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__2));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4(void){
_start:
{
lean_object* v___x_409_; double v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1000u);
v___x_410_ = lean_float_of_nat(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(lean_object* v_cls_411_, uint8_t v_collapsed_412_, lean_object* v_tag_413_, lean_object* v_opts_414_, uint8_t v_clsEnabled_415_, lean_object* v_oldTraces_416_, lean_object* v_msg_417_, lean_object* v_resStartStop_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_513_; 
v_fst_422_ = lean_ctor_get(v_resStartStop_418_, 0);
v_snd_423_ = lean_ctor_get(v_resStartStop_418_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_resStartStop_418_);
if (v_isSharedCheck_513_ == 0)
{
v___x_425_ = v_resStartStop_418_;
v_isShared_426_ = v_isSharedCheck_513_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snd_423_);
lean_inc(v_fst_422_);
lean_dec(v_resStartStop_418_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_513_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v_data_430_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_512_; 
v_fst_433_ = lean_ctor_get(v_snd_423_, 0);
v_snd_434_ = lean_ctor_get(v_snd_423_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_snd_423_);
if (v_isSharedCheck_512_ == 0)
{
v___x_436_ = v_snd_423_;
v_isShared_437_ = v_isSharedCheck_512_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v_snd_423_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_512_;
goto v_resetjp_435_;
}
v___jp_427_:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(v_oldTraces_416_, v_data_430_, v___y_429_, v___y_428_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_432_; 
lean_dec_ref(v___x_431_);
v___x_432_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_fst_422_);
return v___x_432_;
}
else
{
lean_dec(v_fst_422_);
return v___x_431_;
}
}
v_resetjp_435_:
{
lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___y_441_; lean_object* v_a_442_; uint8_t v___y_466_; double v___y_497_; 
v___x_438_ = l_Lean_trace_profiler;
v___x_439_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_opts_414_, v___x_438_);
if (v___x_439_ == 0)
{
v___y_466_ = v___x_439_;
goto v___jp_465_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = l_Lean_trace_profiler_useHeartbeats;
v___x_503_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_opts_414_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; double v___x_506_; double v___x_507_; double v___x_508_; 
v___x_504_ = l_Lean_trace_profiler_threshold;
v___x_505_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(v_opts_414_, v___x_504_);
v___x_506_ = lean_float_of_nat(v___x_505_);
v___x_507_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4);
v___x_508_ = lean_float_div(v___x_506_, v___x_507_);
v___y_497_ = v___x_508_;
goto v___jp_496_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; double v___x_511_; 
v___x_509_ = l_Lean_trace_profiler_threshold;
v___x_510_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(v_opts_414_, v___x_509_);
v___x_511_ = lean_float_of_nat(v___x_510_);
v___y_497_ = v___x_511_;
goto v___jp_496_;
}
}
v___jp_440_:
{
uint8_t v_result_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v_result_443_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(v_fst_422_);
v___x_444_ = l_Lean_TraceResult_toEmoji(v_result_443_);
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 7);
lean_ctor_set(v___x_436_, 1, v___x_446_);
lean_ctor_set(v___x_436_, 0, v___x_445_);
v___x_448_ = v___x_436_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_459_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v_m_450_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 7);
lean_ctor_set(v___x_425_, 1, v_a_442_);
lean_ctor_set(v___x_425_, 0, v___x_448_);
v_m_450_ = v___x_425_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_a_442_);
v_m_450_ = v_reuseFailAlloc_458_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; double v___x_453_; lean_object* v_data_454_; 
v___x_451_ = lean_box(v_result_443_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0);
lean_inc_ref(v_tag_413_);
lean_inc_ref(v___x_452_);
lean_inc(v_cls_411_);
v_data_454_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_454_, 0, v_cls_411_);
lean_ctor_set(v_data_454_, 1, v___x_452_);
lean_ctor_set(v_data_454_, 2, v_tag_413_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3, v___x_453_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3 + 8, v___x_453_);
lean_ctor_set_uint8(v_data_454_, sizeof(void*)*3 + 16, v_collapsed_412_);
if (v___x_439_ == 0)
{
lean_dec_ref(v___x_452_);
lean_dec(v_snd_434_);
lean_dec(v_fst_433_);
lean_dec_ref(v_tag_413_);
lean_dec(v_cls_411_);
v___y_428_ = v_m_450_;
v___y_429_ = v___y_441_;
v_data_430_ = v_data_454_;
goto v___jp_427_;
}
else
{
lean_object* v_data_455_; double v___x_456_; double v___x_457_; 
lean_dec_ref(v_data_454_);
v_data_455_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_455_, 0, v_cls_411_);
lean_ctor_set(v_data_455_, 1, v___x_452_);
lean_ctor_set(v_data_455_, 2, v_tag_413_);
v___x_456_ = lean_unbox_float(v_fst_433_);
lean_dec(v_fst_433_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3, v___x_456_);
v___x_457_ = lean_unbox_float(v_snd_434_);
lean_dec(v_snd_434_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3 + 8, v___x_457_);
lean_ctor_set_uint8(v_data_455_, sizeof(void*)*3 + 16, v_collapsed_412_);
v___y_428_ = v_m_450_;
v___y_429_ = v___y_441_;
v_data_430_ = v_data_455_;
goto v___jp_427_;
}
}
}
}
v___jp_460_:
{
lean_object* v_ref_461_; lean_object* v___x_462_; 
v_ref_461_ = lean_ctor_get(v___y_419_, 5);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
lean_inc(v_fst_422_);
v___x_462_ = lean_apply_4(v_msg_417_, v_fst_422_, v___y_419_, v___y_420_, lean_box(0));
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
lean_inc(v_ref_461_);
v___y_441_ = v_ref_461_;
v_a_442_ = v_a_463_;
goto v___jp_440_;
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v___x_462_);
v___x_464_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3);
lean_inc(v_ref_461_);
v___y_441_ = v_ref_461_;
v_a_442_ = v___x_464_;
goto v___jp_440_;
}
}
v___jp_465_:
{
if (v_clsEnabled_415_ == 0)
{
if (v___y_466_ == 0)
{
lean_object* v___x_467_; lean_object* v_traceState_468_; lean_object* v_env_469_; lean_object* v_nextMacroScope_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_cache_473_; lean_object* v_messages_474_; lean_object* v_infoState_475_; lean_object* v_snapshotTasks_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_436_);
lean_dec(v_snd_434_);
lean_dec(v_fst_433_);
lean_del_object(v___x_425_);
lean_dec_ref(v___y_419_);
lean_dec_ref(v_msg_417_);
lean_dec_ref(v_tag_413_);
lean_dec(v_cls_411_);
v___x_467_ = lean_st_ref_take(v___y_420_);
v_traceState_468_ = lean_ctor_get(v___x_467_, 4);
v_env_469_ = lean_ctor_get(v___x_467_, 0);
v_nextMacroScope_470_ = lean_ctor_get(v___x_467_, 1);
v_ngen_471_ = lean_ctor_get(v___x_467_, 2);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_467_, 3);
v_cache_473_ = lean_ctor_get(v___x_467_, 5);
v_messages_474_ = lean_ctor_get(v___x_467_, 6);
v_infoState_475_ = lean_ctor_get(v___x_467_, 7);
v_snapshotTasks_476_ = lean_ctor_get(v___x_467_, 8);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_495_ == 0)
{
v___x_478_ = v___x_467_;
v_isShared_479_ = v_isSharedCheck_495_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snapshotTasks_476_);
lean_inc(v_infoState_475_);
lean_inc(v_messages_474_);
lean_inc(v_cache_473_);
lean_inc(v_traceState_468_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_nextMacroScope_470_);
lean_inc(v_env_469_);
lean_dec(v___x_467_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_495_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint64_t v_tid_480_; lean_object* v_traces_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_494_; 
v_tid_480_ = lean_ctor_get_uint64(v_traceState_468_, sizeof(void*)*1);
v_traces_481_ = lean_ctor_get(v_traceState_468_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_traceState_468_);
if (v_isSharedCheck_494_ == 0)
{
v___x_483_ = v_traceState_468_;
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_traces_481_);
lean_dec(v_traceState_468_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_416_, v_traces_481_);
lean_dec_ref(v_traces_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_485_);
lean_ctor_set_uint64(v_reuseFailAlloc_493_, sizeof(void*)*1, v_tid_480_);
v___x_487_ = v_reuseFailAlloc_493_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 4, v___x_487_);
v___x_489_ = v___x_478_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_env_469_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_nextMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_cache_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_messages_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_infoState_475_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_snapshotTasks_476_);
v___x_489_ = v_reuseFailAlloc_492_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_st_ref_set(v___y_420_, v___x_489_);
lean_dec(v___y_420_);
v___x_491_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_fst_422_);
return v___x_491_;
}
}
}
}
}
else
{
goto v___jp_460_;
}
}
else
{
goto v___jp_460_;
}
}
v___jp_496_:
{
double v___x_498_; double v___x_499_; double v___x_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unbox_float(v_snd_434_);
v___x_499_ = lean_unbox_float(v_fst_433_);
v___x_500_ = lean_float_sub(v___x_498_, v___x_499_);
v___x_501_ = lean_float_decLt(v___y_497_, v___x_500_);
v___y_466_ = v___x_501_;
goto v___jp_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___boxed(lean_object* v_cls_514_, lean_object* v_collapsed_515_, lean_object* v_tag_516_, lean_object* v_opts_517_, lean_object* v_clsEnabled_518_, lean_object* v_oldTraces_519_, lean_object* v_msg_520_, lean_object* v_resStartStop_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_collapsed_boxed_525_; uint8_t v_clsEnabled_boxed_526_; lean_object* v_res_527_; 
v_collapsed_boxed_525_ = lean_unbox(v_collapsed_515_);
v_clsEnabled_boxed_526_ = lean_unbox(v_clsEnabled_518_);
v_res_527_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v_cls_514_, v_collapsed_boxed_525_, v_tag_516_, v_opts_517_, v_clsEnabled_boxed_526_, v_oldTraces_519_, v_msg_520_, v_resStartStop_521_, v___y_522_, v___y_523_);
lean_dec_ref(v_opts_517_);
return v_res_527_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_528_; double v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1000000000u);
v___x_529_ = lean_float_of_nat(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_562_, lean_object* v_s_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; uint8_t v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; uint8_t v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v_a_578_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; uint8_t v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v_a_598_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; uint8_t v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_a_611_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; uint8_t v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v_a_638_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; uint8_t v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v_a_661_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; uint8_t v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v_a_674_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; uint8_t v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; lean_object* v_element_769_; lean_object* v_children_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_1003_; 
v_element_769_ = lean_ctor_get(v_s_563_, 0);
v_children_770_ = lean_ctor_get(v_s_563_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_s_563_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_772_ = v_s_563_;
v_isShared_773_ = v_isSharedCheck_1003_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_children_770_);
lean_inc(v_element_769_);
lean_dec(v_s_563_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_1003_;
goto v_resetjp_771_;
}
v___jp_567_:
{
lean_object* v___x_579_; double v___x_580_; double v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_579_ = lean_io_get_num_heartbeats();
v___x_580_ = lean_float_of_nat(v___y_576_);
v___x_581_ = lean_float_of_nat(v___x_579_);
v___x_582_ = lean_box_float(v___x_580_);
v___x_583_ = lean_box_float(v___x_581_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_578_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v___y_573_, v___y_575_, v___y_572_, v___y_569_, v___y_571_, v___y_570_, v___y_574_, v___x_585_, v___y_577_, v___y_568_);
lean_dec_ref(v___y_569_);
return v___x_586_;
}
v___jp_587_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_a_598_);
v___y_568_ = v___y_588_;
v___y_569_ = v___y_589_;
v___y_570_ = v___y_592_;
v___y_571_ = v___y_591_;
v___y_572_ = v___y_590_;
v___y_573_ = v___y_593_;
v___y_574_ = v___y_595_;
v___y_575_ = v___y_594_;
v___y_576_ = v___y_596_;
v___y_577_ = v___y_597_;
v_a_578_ = v___x_599_;
goto v___jp_567_;
}
v___jp_600_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_a_611_);
v___y_568_ = v___y_601_;
v___y_569_ = v___y_602_;
v___y_570_ = v___y_605_;
v___y_571_ = v___y_604_;
v___y_572_ = v___y_603_;
v___y_573_ = v___y_606_;
v___y_574_ = v___y_608_;
v___y_575_ = v___y_607_;
v___y_576_ = v___y_609_;
v___y_577_ = v___y_610_;
v_a_578_ = v___x_612_;
goto v___jp_567_;
}
v___jp_613_:
{
if (lean_obj_tag(v___y_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___y_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___y_624_);
v___y_588_ = v___y_614_;
v___y_589_ = v___y_615_;
v___y_590_ = v___y_618_;
v___y_591_ = v___y_617_;
v___y_592_ = v___y_616_;
v___y_593_ = v___y_619_;
v___y_594_ = v___y_621_;
v___y_595_ = v___y_620_;
v___y_596_ = v___y_622_;
v___y_597_ = v___y_623_;
v_a_598_ = v_a_625_;
goto v___jp_587_;
}
else
{
lean_object* v_a_626_; 
v_a_626_ = lean_ctor_get(v___y_624_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v___y_624_);
v___y_601_ = v___y_614_;
v___y_602_ = v___y_615_;
v___y_603_ = v___y_618_;
v___y_604_ = v___y_617_;
v___y_605_ = v___y_616_;
v___y_606_ = v___y_619_;
v___y_607_ = v___y_621_;
v___y_608_ = v___y_620_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_623_;
v_a_611_ = v_a_626_;
goto v___jp_600_;
}
}
v___jp_627_:
{
lean_object* v___x_639_; double v___x_640_; double v___x_641_; double v___x_642_; double v___x_643_; double v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_639_ = lean_io_mono_nanos_now();
v___x_640_ = lean_float_of_nat(v___y_630_);
v___x_641_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_642_ = lean_float_div(v___x_640_, v___x_641_);
v___x_643_ = lean_float_of_nat(v___x_639_);
v___x_644_ = lean_float_div(v___x_643_, v___x_641_);
v___x_645_ = lean_box_float(v___x_642_);
v___x_646_ = lean_box_float(v___x_644_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_a_638_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v___y_634_, v___y_636_, v___y_633_, v___y_629_, v___y_632_, v___y_631_, v___y_635_, v___x_648_, v___y_637_, v___y_628_);
lean_dec_ref(v___y_629_);
return v___x_649_;
}
v___jp_650_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_a_661_);
v___y_628_ = v___y_651_;
v___y_629_ = v___y_653_;
v___y_630_ = v___y_652_;
v___y_631_ = v___y_656_;
v___y_632_ = v___y_655_;
v___y_633_ = v___y_654_;
v___y_634_ = v___y_657_;
v___y_635_ = v___y_659_;
v___y_636_ = v___y_658_;
v___y_637_ = v___y_660_;
v_a_638_ = v___x_662_;
goto v___jp_627_;
}
v___jp_663_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v_a_674_);
v___y_628_ = v___y_664_;
v___y_629_ = v___y_666_;
v___y_630_ = v___y_665_;
v___y_631_ = v___y_669_;
v___y_632_ = v___y_668_;
v___y_633_ = v___y_667_;
v___y_634_ = v___y_670_;
v___y_635_ = v___y_672_;
v___y_636_ = v___y_671_;
v___y_637_ = v___y_673_;
v_a_638_ = v___x_675_;
goto v___jp_627_;
}
v___jp_676_:
{
if (lean_obj_tag(v___y_687_) == 0)
{
lean_object* v_a_688_; 
v_a_688_ = lean_ctor_get(v___y_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v___y_687_);
v___y_651_ = v___y_677_;
v___y_652_ = v___y_679_;
v___y_653_ = v___y_678_;
v___y_654_ = v___y_682_;
v___y_655_ = v___y_681_;
v___y_656_ = v___y_680_;
v___y_657_ = v___y_683_;
v___y_658_ = v___y_685_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_686_;
v_a_661_ = v_a_688_;
goto v___jp_650_;
}
else
{
lean_object* v_a_689_; 
v_a_689_ = lean_ctor_get(v___y_687_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___y_687_);
v___y_664_ = v___y_677_;
v___y_665_ = v___y_679_;
v___y_666_ = v___y_678_;
v___y_667_ = v___y_682_;
v___y_668_ = v___y_681_;
v___y_669_ = v___y_680_;
v___y_670_ = v___y_683_;
v___y_671_ = v___y_685_;
v___y_672_ = v___y_684_;
v___y_673_ = v___y_686_;
v_a_674_ = v_a_689_;
goto v___jp_663_;
}
}
v___jp_690_:
{
lean_object* v___x_703_; 
v___x_703_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(v___y_691_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
v___x_705_ = l_Lean_trace_profiler_useHeartbeats;
v___x_706_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_693_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_io_mono_nanos_now();
lean_inc(v___y_691_);
lean_inc_ref(v___y_698_);
v___x_708_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_696_, v___y_698_, v___y_691_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_dec_ref(v___x_708_);
if (lean_obj_tag(v___y_697_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_val_709_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_val_709_);
lean_dec_ref(v___y_697_);
v___x_710_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
v___x_711_ = l_Lean_Name_mkStr2(v___y_692_, v___x_710_);
lean_inc(v___x_711_);
v___x_712_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_711_, v___y_698_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; uint8_t v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec(v___x_711_);
lean_dec(v_val_709_);
lean_dec(v___y_699_);
v___x_715_ = lean_box(0);
v___y_651_ = v___y_691_;
v___y_652_ = v___x_707_;
v___y_653_ = v___y_693_;
v___y_654_ = v___y_694_;
v___y_655_ = v___y_700_;
v___y_656_ = v_a_704_;
v___y_657_ = v___y_695_;
v___y_658_ = v___y_702_;
v___y_659_ = v___y_701_;
v___y_660_ = v___y_698_;
v_a_661_ = v___x_715_;
goto v___jp_650_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_Elab_InfoTree_format(v_val_709_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v___y_699_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v___x_719_ = l_Lean_MessageData_ofFormat(v_a_718_);
v___x_720_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_711_, v___x_719_, v___y_698_, v___y_691_);
v___y_677_ = v___y_691_;
v___y_678_ = v___y_693_;
v___y_679_ = v___x_707_;
v___y_680_ = v_a_704_;
v___y_681_ = v___y_700_;
v___y_682_ = v___y_694_;
v___y_683_ = v___y_695_;
v___y_684_ = v___y_701_;
v___y_685_ = v___y_702_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_720_;
goto v___jp_676_;
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
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___y_699_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___y_664_ = v___y_691_;
v___y_665_ = v___x_707_;
v___y_666_ = v___y_693_;
v___y_667_ = v___y_694_;
v___y_668_ = v___y_700_;
v___y_669_ = v_a_704_;
v___y_670_ = v___y_695_;
v___y_671_ = v___y_702_;
v___y_672_ = v___y_701_;
v___y_673_ = v___y_698_;
v_a_674_ = v___x_729_;
goto v___jp_663_;
}
}
}
}
}
else
{
lean_object* v_a_732_; 
lean_dec(v___x_711_);
lean_dec(v_val_709_);
lean_dec(v___y_699_);
v_a_732_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_712_);
v___y_664_ = v___y_691_;
v___y_665_ = v___x_707_;
v___y_666_ = v___y_693_;
v___y_667_ = v___y_694_;
v___y_668_ = v___y_700_;
v___y_669_ = v_a_704_;
v___y_670_ = v___y_695_;
v___y_671_ = v___y_702_;
v___y_672_ = v___y_701_;
v___y_673_ = v___y_698_;
v_a_674_ = v_a_732_;
goto v___jp_663_;
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v___y_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_692_);
v___x_733_ = lean_box(0);
v___y_651_ = v___y_691_;
v___y_652_ = v___x_707_;
v___y_653_ = v___y_693_;
v___y_654_ = v___y_694_;
v___y_655_ = v___y_700_;
v___y_656_ = v_a_704_;
v___y_657_ = v___y_695_;
v___y_658_ = v___y_702_;
v___y_659_ = v___y_701_;
v___y_660_ = v___y_698_;
v_a_661_ = v___x_733_;
goto v___jp_650_;
}
}
else
{
lean_dec(v___y_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_692_);
v___y_677_ = v___y_691_;
v___y_678_ = v___y_693_;
v___y_679_ = v___x_707_;
v___y_680_ = v_a_704_;
v___y_681_ = v___y_700_;
v___y_682_ = v___y_694_;
v___y_683_ = v___y_695_;
v___y_684_ = v___y_701_;
v___y_685_ = v___y_702_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_708_;
goto v___jp_676_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_io_get_num_heartbeats();
lean_inc(v___y_691_);
lean_inc_ref(v___y_698_);
v___x_735_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_696_, v___y_698_, v___y_691_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec_ref(v___x_735_);
if (lean_obj_tag(v___y_697_) == 1)
{
lean_object* v_val_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_val_736_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_val_736_);
lean_dec_ref(v___y_697_);
v___x_737_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
v___x_738_ = l_Lean_Name_mkStr2(v___y_692_, v___x_737_);
lean_inc(v___x_738_);
v___x_739_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_738_, v___y_698_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; uint8_t v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v___x_739_);
v___x_741_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v___x_738_);
lean_dec(v_val_736_);
lean_dec(v___y_699_);
v___x_742_ = lean_box(0);
v___y_588_ = v___y_691_;
v___y_589_ = v___y_693_;
v___y_590_ = v___y_694_;
v___y_591_ = v___y_700_;
v___y_592_ = v_a_704_;
v___y_593_ = v___y_695_;
v___y_594_ = v___y_702_;
v___y_595_ = v___y_701_;
v___y_596_ = v___x_734_;
v___y_597_ = v___y_698_;
v_a_598_ = v___x_742_;
goto v___jp_587_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = l_Lean_Elab_InfoTree_format(v_val_736_, v___x_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v___y_699_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_MessageData_ofFormat(v_a_745_);
v___x_747_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_738_, v___x_746_, v___y_698_, v___y_691_);
v___y_614_ = v___y_691_;
v___y_615_ = v___y_693_;
v___y_616_ = v_a_704_;
v___y_617_ = v___y_700_;
v___y_618_ = v___y_694_;
v___y_619_ = v___y_695_;
v___y_620_ = v___y_701_;
v___y_621_ = v___y_702_;
v___y_622_ = v___x_734_;
v___y_623_ = v___y_698_;
v___y_624_ = v___x_747_;
goto v___jp_613_;
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_738_);
v_a_748_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_758_ == 0)
{
v___x_750_ = v___x_744_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_io_error_to_string(v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 3);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_757_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = l_Lean_MessageData_ofFormat(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___y_699_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___y_601_ = v___y_691_;
v___y_602_ = v___y_693_;
v___y_603_ = v___y_694_;
v___y_604_ = v___y_700_;
v___y_605_ = v_a_704_;
v___y_606_ = v___y_695_;
v___y_607_ = v___y_702_;
v___y_608_ = v___y_701_;
v___y_609_ = v___x_734_;
v___y_610_ = v___y_698_;
v_a_611_ = v___x_756_;
goto v___jp_600_;
}
}
}
}
}
else
{
lean_object* v_a_759_; 
lean_dec(v___x_738_);
lean_dec(v_val_736_);
lean_dec(v___y_699_);
v_a_759_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_739_);
v___y_601_ = v___y_691_;
v___y_602_ = v___y_693_;
v___y_603_ = v___y_694_;
v___y_604_ = v___y_700_;
v___y_605_ = v_a_704_;
v___y_606_ = v___y_695_;
v___y_607_ = v___y_702_;
v___y_608_ = v___y_701_;
v___y_609_ = v___x_734_;
v___y_610_ = v___y_698_;
v_a_611_ = v_a_759_;
goto v___jp_600_;
}
}
else
{
lean_object* v___x_760_; 
lean_dec(v___y_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_692_);
v___x_760_ = lean_box(0);
v___y_588_ = v___y_691_;
v___y_589_ = v___y_693_;
v___y_590_ = v___y_694_;
v___y_591_ = v___y_700_;
v___y_592_ = v_a_704_;
v___y_593_ = v___y_695_;
v___y_594_ = v___y_702_;
v___y_595_ = v___y_701_;
v___y_596_ = v___x_734_;
v___y_597_ = v___y_698_;
v_a_598_ = v___x_760_;
goto v___jp_587_;
}
}
else
{
lean_dec(v___y_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_692_);
v___y_614_ = v___y_691_;
v___y_615_ = v___y_693_;
v___y_616_ = v_a_704_;
v___y_617_ = v___y_700_;
v___y_618_ = v___y_694_;
v___y_619_ = v___y_695_;
v___y_620_ = v___y_701_;
v___y_621_ = v___y_702_;
v___y_622_ = v___x_734_;
v___y_623_ = v___y_698_;
v___y_624_ = v___x_735_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_701_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
v_a_761_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_703_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_703_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v_resetjp_771_:
{
lean_object* v_desc_774_; lean_object* v_diagnostics_775_; lean_object* v_infoTree_x3f_776_; lean_object* v_desc_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___x_939_; 
v_desc_774_ = lean_ctor_get(v_element_769_, 0);
lean_inc_ref(v_desc_774_);
v_diagnostics_775_ = lean_ctor_get(v_element_769_, 1);
lean_inc_ref(v_diagnostics_775_);
v_infoTree_x3f_776_ = lean_ctor_get(v_element_769_, 2);
lean_inc(v_infoTree_x3f_776_);
lean_dec_ref(v_element_769_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v_desc_774_);
switch(lean_obj_tag(v_range_x3f_562_))
{
case 0:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v_desc_778_ = v___x_941_;
v___y_779_ = v_a_564_;
v___y_780_ = v_a_565_;
goto v___jp_777_;
}
case 1:
{
lean_object* v_range_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1000_; 
v_range_942_ = lean_ctor_get(v_range_x3f_562_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_range_x3f_562_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_944_ = v_range_x3f_562_;
v_isShared_945_ = v_isSharedCheck_1000_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_range_942_);
lean_dec(v_range_x3f_562_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1000_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_fileMap_946_; lean_object* v_start_947_; lean_object* v_stop_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_999_; 
v_fileMap_946_ = lean_ctor_get(v_a_564_, 1);
v_start_947_ = lean_ctor_get(v_range_942_, 0);
v_stop_948_ = lean_ctor_get(v_range_942_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_range_942_);
if (v_isSharedCheck_999_ == 0)
{
v___x_950_ = v_range_942_;
v_isShared_951_ = v_isSharedCheck_999_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_stop_948_);
lean_inc(v_start_947_);
lean_dec(v_range_942_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_999_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v_line_953_; lean_object* v_column_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_998_; 
lean_inc_ref(v_fileMap_946_);
v___x_952_ = l_Lean_FileMap_toPosition(v_fileMap_946_, v_start_947_);
lean_dec(v_start_947_);
v_line_953_ = lean_ctor_get(v___x_952_, 0);
v_column_954_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_998_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_998_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_column_954_);
lean_inc(v_line_953_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_998_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_line_959_; lean_object* v_column_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_997_; 
lean_inc_ref(v_fileMap_946_);
v___x_958_ = l_Lean_FileMap_toPosition(v_fileMap_946_, v_stop_948_);
lean_dec(v_stop_948_);
v_line_959_ = lean_ctor_get(v___x_958_, 0);
v_column_960_ = lean_ctor_get(v___x_958_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_997_ == 0)
{
v___x_962_ = v___x_958_;
v_isShared_963_ = v_isSharedCheck_997_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_column_960_);
lean_inc(v_line_959_);
lean_dec(v___x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_997_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11));
v___x_965_ = l_Nat_reprFast(v_line_953_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 3);
lean_ctor_set(v___x_944_, 0, v___x_965_);
v___x_967_ = v___x_944_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_996_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 5);
lean_ctor_set(v___x_962_, 1, v___x_967_);
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_969_ = v___x_962_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_995_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 5);
lean_ctor_set(v___x_956_, 1, v___x_970_);
lean_ctor_set(v___x_956_, 0, v___x_969_);
v___x_972_ = v___x_956_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_994_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = l_Nat_reprFast(v_column_954_);
v___x_974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 5);
lean_ctor_set(v___x_950_, 1, v___x_974_);
lean_ctor_set(v___x_950_, 0, v___x_972_);
v___x_976_ = v___x_950_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_993_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Nat_reprFast(v_line_959_);
v___x_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_964_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_970_);
v___x_985_ = l_Nat_reprFast(v_column_960_);
v___x_986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_984_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_977_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_980_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_939_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v_desc_778_ = v___x_992_;
v___y_779_ = v_a_564_;
v___y_780_ = v_a_565_;
goto v___jp_777_;
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
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20));
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_939_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v_desc_778_ = v___x_1002_;
v___y_779_ = v_a_564_;
v___y_780_ = v_a_565_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v_msgLog_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_937_; 
v_msgLog_781_ = lean_ctor_get(v_diagnostics_775_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_diagnostics_775_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_diagnostics_775_, 1);
lean_dec(v_unused_938_);
v___x_783_ = v_diagnostics_775_;
v_isShared_784_ = v_isSharedCheck_937_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_msgLog_781_);
lean_dec(v_diagnostics_775_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_937_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = l_Lean_MessageLog_toList(v_msgLog_781_);
lean_dec_ref(v_msgLog_781_);
v___x_786_ = lean_box(0);
v___x_787_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_785_, v___x_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_options_788_; lean_object* v_a_789_; lean_object* v_ref_790_; uint8_t v_hasTrace_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_options_788_ = lean_ctor_get(v___y_779_, 2);
v_a_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_787_);
v_ref_790_ = lean_ctor_get(v___y_779_, 5);
v_hasTrace_791_ = lean_ctor_get_uint8(v_options_788_, sizeof(void*)*1);
v___x_792_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2));
v___x_793_ = lean_array_to_list(v_children_770_);
if (v_hasTrace_791_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v_a_789_);
lean_dec(v_desc_778_);
lean_del_object(v___x_772_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_794_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_793_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_794_, 0);
lean_dec(v_unused_849_);
v___x_796_ = v___x_794_;
v_isShared_797_ = v_isSharedCheck_848_;
goto v_resetjp_795_;
}
else
{
lean_dec(v___x_794_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_848_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
if (lean_obj_tag(v_infoTree_x3f_776_) == 1)
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_796_);
v_val_798_ = lean_ctor_get(v_infoTree_x3f_776_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_infoTree_x3f_776_);
if (v_isSharedCheck_843_ == 0)
{
v___x_800_ = v_infoTree_x3f_776_;
v_isShared_801_ = v_isSharedCheck_843_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v_infoTree_x3f_776_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_843_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_803_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_802_, v___y_779_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_834_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_834_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_834_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_834_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; 
v___x_808_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_del_object(v___x_800_);
lean_dec(v_val_798_);
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
v___x_809_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_806_);
v___x_813_ = lean_box(0);
v___x_814_ = l_Lean_Elab_InfoTree_format(v_val_798_, v___x_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_del_object(v___x_800_);
lean_del_object(v___x_783_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Lean_MessageData_ofFormat(v_a_815_);
v___x_817_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_802_, v___x_816_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v___x_817_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_833_; 
lean_inc(v_ref_790_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
v_a_818_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_833_ == 0)
{
v___x_820_ = v___x_814_;
v_isShared_821_ = v_isSharedCheck_833_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_833_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_io_error_to_string(v_a_818_);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 3);
lean_ctor_set(v___x_800_, 0, v___x_822_);
v___x_824_ = v___x_800_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_832_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_MessageData_ofFormat(v___x_824_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_825_);
lean_ctor_set(v___x_783_, 0, v_ref_790_);
v___x_827_ = v___x_783_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_ref_790_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_827_);
v___x_829_ = v___x_820_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
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
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_del_object(v___x_800_);
lean_dec(v_val_798_);
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
v_a_835_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_803_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_803_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_infoTree_x3f_776_);
v___x_844_ = lean_box(0);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_844_);
v___x_846_ = v___x_796_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_infoTree_x3f_776_);
return v___x_794_;
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5));
v___x_851_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_850_, v___y_779_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
v___x_853_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7));
v___x_854_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___x_853_, v_a_789_);
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 5);
lean_ctor_set(v___x_783_, 1, v___x_854_);
lean_ctor_set(v___x_783_, 0, v_desc_778_);
v___x_856_ = v___x_783_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_desc_778_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_920_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___f_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___f_857_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_857_, 0, v___x_856_);
v___x_858_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1));
v___x_859_ = lean_unbox(v_a_852_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = l_Lean_trace_profiler;
v___x_861_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_options_788_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v___f_857_);
lean_dec(v_a_852_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_862_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_793_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_916_; 
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_862_, 0);
lean_dec(v_unused_917_);
v___x_864_ = v___x_862_;
v_isShared_865_ = v_isSharedCheck_916_;
goto v_resetjp_863_;
}
else
{
lean_dec(v___x_862_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_916_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
if (lean_obj_tag(v_infoTree_x3f_776_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_864_);
v_val_866_ = lean_ctor_get(v_infoTree_x3f_776_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_infoTree_x3f_776_);
if (v_isSharedCheck_911_ == 0)
{
v___x_868_ = v_infoTree_x3f_776_;
v_isShared_869_ = v_isSharedCheck_911_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v_infoTree_x3f_776_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_911_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_871_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_870_, v___y_779_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_902_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_902_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_902_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_902_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
uint8_t v___x_876_; 
v___x_876_ = lean_unbox(v_a_872_);
lean_dec(v_a_872_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_del_object(v___x_868_);
lean_dec(v_val_866_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_del_object(v___x_772_);
v___x_877_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_877_);
v___x_879_ = v___x_874_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_del_object(v___x_874_);
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_Elab_InfoTree_format(v_val_866_, v___x_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_del_object(v___x_868_);
lean_del_object(v___x_772_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___x_884_ = l_Lean_MessageData_ofFormat(v_a_883_);
v___x_885_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_870_, v___x_884_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v___x_885_;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_901_; 
lean_inc(v_ref_790_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
v_a_886_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_901_ == 0)
{
v___x_888_ = v___x_882_;
v_isShared_889_ = v_isSharedCheck_901_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_901_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_io_error_to_string(v_a_886_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 3);
lean_ctor_set(v___x_868_, 0, v___x_890_);
v___x_892_ = v___x_868_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_900_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = l_Lean_MessageData_ofFormat(v___x_892_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_893_);
lean_ctor_set(v___x_772_, 0, v_ref_790_);
v___x_895_ = v___x_772_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_ref_790_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_895_);
v___x_897_ = v___x_888_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
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
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_868_);
lean_dec(v_val_866_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_del_object(v___x_772_);
v_a_903_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_871_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_871_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
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
}
else
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_infoTree_x3f_776_);
lean_del_object(v___x_772_);
v___x_912_ = lean_box(0);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_912_);
v___x_914_ = v___x_864_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_infoTree_x3f_776_);
lean_del_object(v___x_772_);
return v___x_862_;
}
}
else
{
uint8_t v___x_918_; 
lean_inc(v_ref_790_);
lean_inc_ref(v_options_788_);
lean_del_object(v___x_772_);
v___x_918_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
v___y_691_ = v___y_780_;
v___y_692_ = v___x_792_;
v___y_693_ = v_options_788_;
v___y_694_ = v___x_858_;
v___y_695_ = v___x_850_;
v___y_696_ = v___x_793_;
v___y_697_ = v_infoTree_x3f_776_;
v___y_698_ = v___y_779_;
v___y_699_ = v_ref_790_;
v___y_700_ = v___x_918_;
v___y_701_ = v___f_857_;
v___y_702_ = v_hasTrace_791_;
goto v___jp_690_;
}
}
else
{
uint8_t v___x_919_; 
lean_inc(v_ref_790_);
lean_inc_ref(v_options_788_);
lean_del_object(v___x_772_);
v___x_919_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
v___y_691_ = v___y_780_;
v___y_692_ = v___x_792_;
v___y_693_ = v_options_788_;
v___y_694_ = v___x_858_;
v___y_695_ = v___x_850_;
v___y_696_ = v___x_793_;
v___y_697_ = v_infoTree_x3f_776_;
v___y_698_ = v___y_779_;
v___y_699_ = v_ref_790_;
v___y_700_ = v___x_919_;
v___y_701_ = v___f_857_;
v___y_702_ = v_hasTrace_791_;
goto v___jp_690_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v___x_793_);
lean_dec(v_a_789_);
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_desc_778_);
lean_dec(v_infoTree_x3f_776_);
lean_del_object(v___x_772_);
v_a_921_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_851_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_851_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_783_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_desc_778_);
lean_dec(v_infoTree_x3f_776_);
lean_del_object(v___x_772_);
lean_dec_ref(v_children_770_);
v_a_929_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_787_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_787_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
if (lean_obj_tag(v_as_1004_) == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
else
{
lean_object* v_head_1010_; lean_object* v_tail_1011_; lean_object* v_reportingRange_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_head_1010_ = lean_ctor_get(v_as_1004_, 0);
lean_inc(v_head_1010_);
v_tail_1011_ = lean_ctor_get(v_as_1004_, 1);
lean_inc(v_tail_1011_);
lean_dec_ref(v_as_1004_);
v_reportingRange_1012_ = lean_ctor_get(v_head_1010_, 1);
lean_inc(v_reportingRange_1012_);
v___x_1013_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_1010_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
v___x_1014_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_1012_, v___x_1013_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref(v___x_1014_);
v_as_1004_ = v_tail_1011_;
goto _start;
}
else
{
lean_dec(v_tail_1011_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_1016_, v___y_1017_, v___y_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_1021_, lean_object* v_s_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_1021_, v_s_1022_, v_a_1023_, v_a_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_1027_, v_x_1028_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_1033_, v_x_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11(lean_object* v_00_u03b1_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_x_1040_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11(v_00_u03b1_1045_, v_x_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_box(2);
v___x_1056_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_1055_, v_s_1051_, v_a_1052_, v_a_1053_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Language_SnapshotTree_trace(v_s_1057_, v_a_1058_, v_a_1059_);
return v_res_1061_;
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

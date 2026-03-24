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
lean_object* v_fileName_297_; lean_object* v_fileMap_298_; lean_object* v_options_299_; lean_object* v_currRecDepth_300_; lean_object* v_maxRecDepth_301_; lean_object* v_ref_302_; lean_object* v_currNamespace_303_; lean_object* v_openDecls_304_; lean_object* v_initHeartbeats_305_; lean_object* v_maxHeartbeats_306_; lean_object* v_quotContext_307_; lean_object* v_currMacroScope_308_; uint8_t v_diag_309_; lean_object* v_cancelTk_x3f_310_; uint8_t v_suppressElabErrors_311_; lean_object* v_inheritedTraceOptions_312_; lean_object* v___x_313_; lean_object* v_traceState_314_; lean_object* v_traces_315_; lean_object* v_ref_316_; lean_object* v___x_317_; lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; lean_object* v_msg_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_361_; 
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
v___x_313_ = lean_st_ref_get(v___y_295_);
v_traceState_314_ = lean_ctor_get(v___x_313_, 4);
lean_inc_ref(v_traceState_314_);
lean_dec(v___x_313_);
v_traces_315_ = lean_ctor_get(v_traceState_314_, 0);
lean_inc_ref(v_traces_315_);
lean_dec_ref(v_traceState_314_);
v_ref_316_ = l_Lean_replaceRef(v_ref_292_, v_ref_302_);
lean_inc_ref(v_inheritedTraceOptions_312_);
lean_inc(v_cancelTk_x3f_310_);
lean_inc(v_currMacroScope_308_);
lean_inc(v_quotContext_307_);
lean_inc(v_maxHeartbeats_306_);
lean_inc(v_initHeartbeats_305_);
lean_inc(v_openDecls_304_);
lean_inc(v_currNamespace_303_);
lean_inc(v_maxRecDepth_301_);
lean_inc(v_currRecDepth_300_);
lean_inc_ref(v_options_299_);
lean_inc_ref(v_fileMap_298_);
lean_inc_ref(v_fileName_297_);
v___x_317_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_317_, 0, v_fileName_297_);
lean_ctor_set(v___x_317_, 1, v_fileMap_298_);
lean_ctor_set(v___x_317_, 2, v_options_299_);
lean_ctor_set(v___x_317_, 3, v_currRecDepth_300_);
lean_ctor_set(v___x_317_, 4, v_maxRecDepth_301_);
lean_ctor_set(v___x_317_, 5, v_ref_316_);
lean_ctor_set(v___x_317_, 6, v_currNamespace_303_);
lean_ctor_set(v___x_317_, 7, v_openDecls_304_);
lean_ctor_set(v___x_317_, 8, v_initHeartbeats_305_);
lean_ctor_set(v___x_317_, 9, v_maxHeartbeats_306_);
lean_ctor_set(v___x_317_, 10, v_quotContext_307_);
lean_ctor_set(v___x_317_, 11, v_currMacroScope_308_);
lean_ctor_set(v___x_317_, 12, v_cancelTk_x3f_310_);
lean_ctor_set(v___x_317_, 13, v_inheritedTraceOptions_312_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*14, v_diag_309_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*14 + 1, v_suppressElabErrors_311_);
v___x_318_ = l_Lean_PersistentArray_toArray___redArg(v_traces_315_);
lean_dec_ref(v_traces_315_);
v_sz_319_ = lean_array_size(v___x_318_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10_spec__11(v_sz_319_, v___x_320_, v___x_318_);
v_msg_322_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_322_, 0, v_data_291_);
lean_ctor_set(v_msg_322_, 1, v_msg_293_);
lean_ctor_set(v_msg_322_, 2, v___x_321_);
v___x_323_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__3(v_msg_322_, v___x_317_, v___y_295_);
lean_dec_ref(v___x_317_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_361_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_361_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_361_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v_traceState_329_; lean_object* v_env_330_; lean_object* v_nextMacroScope_331_; lean_object* v_ngen_332_; lean_object* v_auxDeclNGen_333_; lean_object* v_cache_334_; lean_object* v_messages_335_; lean_object* v_infoState_336_; lean_object* v_snapshotTasks_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_360_; 
v___x_328_ = lean_st_ref_take(v___y_295_);
v_traceState_329_ = lean_ctor_get(v___x_328_, 4);
v_env_330_ = lean_ctor_get(v___x_328_, 0);
v_nextMacroScope_331_ = lean_ctor_get(v___x_328_, 1);
v_ngen_332_ = lean_ctor_get(v___x_328_, 2);
v_auxDeclNGen_333_ = lean_ctor_get(v___x_328_, 3);
v_cache_334_ = lean_ctor_get(v___x_328_, 5);
v_messages_335_ = lean_ctor_get(v___x_328_, 6);
v_infoState_336_ = lean_ctor_get(v___x_328_, 7);
v_snapshotTasks_337_ = lean_ctor_get(v___x_328_, 8);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_360_ == 0)
{
v___x_339_ = v___x_328_;
v_isShared_340_ = v_isSharedCheck_360_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snapshotTasks_337_);
lean_inc(v_infoState_336_);
lean_inc(v_messages_335_);
lean_inc(v_cache_334_);
lean_inc(v_traceState_329_);
lean_inc(v_auxDeclNGen_333_);
lean_inc(v_ngen_332_);
lean_inc(v_nextMacroScope_331_);
lean_inc(v_env_330_);
lean_dec(v___x_328_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_360_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
uint64_t v_tid_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_358_; 
v_tid_341_ = lean_ctor_get_uint64(v_traceState_329_, sizeof(void*)*1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_traceState_329_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_traceState_329_, 0);
lean_dec(v_unused_359_);
v___x_343_ = v_traceState_329_;
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
else
{
lean_dec(v_traceState_329_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_ref_292_);
lean_ctor_set(v___x_345_, 1, v_a_324_);
v___x_346_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_290_, v___x_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_346_);
lean_ctor_set_uint64(v_reuseFailAlloc_357_, sizeof(void*)*1, v_tid_341_);
v___x_348_ = v_reuseFailAlloc_357_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v___x_348_);
v___x_350_ = v___x_339_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_env_330_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_nextMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_ngen_332_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_auxDeclNGen_333_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v_cache_334_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_messages_335_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_infoState_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v_snapshotTasks_337_);
v___x_350_ = v_reuseFailAlloc_356_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_st_ref_set(v___y_295_, v___x_350_);
v___x_352_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_352_);
v___x_354_ = v___x_326_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10___boxed(lean_object* v_oldTraces_362_, lean_object* v_data_363_, lean_object* v_ref_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(v_oldTraces_362_, v_data_363_, v_ref_364_, v_msg_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(lean_object* v_e_370_){
_start:
{
if (lean_obj_tag(v_e_370_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 2;
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9___boxed(lean_object* v_e_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(v_e_373_);
lean_dec_ref(v_e_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v_x_376_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v_x_376_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_x_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v_x_376_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v_x_376_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v_x_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg___boxed(lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_x_394_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__2));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4(void){
_start:
{
lean_object* v___x_403_; double v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1000u);
v___x_404_ = lean_float_of_nat(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(lean_object* v_cls_405_, uint8_t v_collapsed_406_, lean_object* v_tag_407_, lean_object* v_opts_408_, uint8_t v_clsEnabled_409_, lean_object* v_oldTraces_410_, lean_object* v_msg_411_, lean_object* v_resStartStop_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_507_; 
v_fst_416_ = lean_ctor_get(v_resStartStop_412_, 0);
v_snd_417_ = lean_ctor_get(v_resStartStop_412_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_resStartStop_412_);
if (v_isSharedCheck_507_ == 0)
{
v___x_419_ = v_resStartStop_412_;
v_isShared_420_ = v_isSharedCheck_507_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
lean_dec(v_resStartStop_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_507_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v_data_424_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_506_; 
v_fst_427_ = lean_ctor_get(v_snd_417_, 0);
v_snd_428_ = lean_ctor_get(v_snd_417_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_snd_417_);
if (v_isSharedCheck_506_ == 0)
{
v___x_430_ = v_snd_417_;
v_isShared_431_ = v_isSharedCheck_506_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_snd_417_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_506_;
goto v_resetjp_429_;
}
v___jp_421_:
{
lean_object* v___x_425_; 
lean_inc(v___y_422_);
v___x_425_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__10(v_oldTraces_410_, v_data_424_, v___y_422_, v___y_423_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; 
lean_dec_ref(v___x_425_);
v___x_426_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_fst_416_);
return v___x_426_;
}
else
{
lean_dec(v_fst_416_);
return v___x_425_;
}
}
v_resetjp_429_:
{
lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___y_435_; lean_object* v_a_436_; uint8_t v___y_460_; double v___y_491_; 
v___x_432_ = l_Lean_trace_profiler;
v___x_433_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_opts_408_, v___x_432_);
if (v___x_433_ == 0)
{
v___y_460_ = v___x_433_;
goto v___jp_459_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = l_Lean_trace_profiler_useHeartbeats;
v___x_497_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_opts_408_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; double v___x_500_; double v___x_501_; double v___x_502_; 
v___x_498_ = l_Lean_trace_profiler_threshold;
v___x_499_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(v_opts_408_, v___x_498_);
v___x_500_ = lean_float_of_nat(v___x_499_);
v___x_501_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__4);
v___x_502_ = lean_float_div(v___x_500_, v___x_501_);
v___y_491_ = v___x_502_;
goto v___jp_490_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; double v___x_505_; 
v___x_503_ = l_Lean_trace_profiler_threshold;
v___x_504_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__12(v_opts_408_, v___x_503_);
v___x_505_ = lean_float_of_nat(v___x_504_);
v___y_491_ = v___x_505_;
goto v___jp_490_;
}
}
v___jp_434_:
{
uint8_t v_result_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v_result_437_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__9(v_fst_416_);
v___x_438_ = l_Lean_TraceResult_toEmoji(v_result_437_);
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__1);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 7);
lean_ctor_set(v___x_430_, 1, v___x_440_);
lean_ctor_set(v___x_430_, 0, v___x_439_);
v___x_442_ = v___x_430_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_453_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v_m_444_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 7);
lean_ctor_set(v___x_419_, 1, v_a_436_);
lean_ctor_set(v___x_419_, 0, v___x_442_);
v_m_444_ = v___x_419_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_a_436_);
v_m_444_ = v_reuseFailAlloc_452_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; double v___x_447_; lean_object* v_data_448_; 
v___x_445_ = lean_box(v_result_437_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__0);
lean_inc_ref(v_tag_407_);
lean_inc_ref(v___x_446_);
lean_inc(v_cls_405_);
v_data_448_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_448_, 0, v_cls_405_);
lean_ctor_set(v_data_448_, 1, v___x_446_);
lean_ctor_set(v_data_448_, 2, v_tag_407_);
lean_ctor_set_float(v_data_448_, sizeof(void*)*3, v___x_447_);
lean_ctor_set_float(v_data_448_, sizeof(void*)*3 + 8, v___x_447_);
lean_ctor_set_uint8(v_data_448_, sizeof(void*)*3 + 16, v_collapsed_406_);
if (v___x_433_ == 0)
{
lean_dec_ref(v___x_446_);
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
lean_dec_ref(v_tag_407_);
lean_dec(v_cls_405_);
v___y_422_ = v___y_435_;
v___y_423_ = v_m_444_;
v_data_424_ = v_data_448_;
goto v___jp_421_;
}
else
{
lean_object* v_data_449_; double v___x_450_; double v___x_451_; 
lean_dec_ref(v_data_448_);
v_data_449_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_449_, 0, v_cls_405_);
lean_ctor_set(v_data_449_, 1, v___x_446_);
lean_ctor_set(v_data_449_, 2, v_tag_407_);
v___x_450_ = lean_unbox_float(v_fst_427_);
lean_dec(v_fst_427_);
lean_ctor_set_float(v_data_449_, sizeof(void*)*3, v___x_450_);
v___x_451_ = lean_unbox_float(v_snd_428_);
lean_dec(v_snd_428_);
lean_ctor_set_float(v_data_449_, sizeof(void*)*3 + 8, v___x_451_);
lean_ctor_set_uint8(v_data_449_, sizeof(void*)*3 + 16, v_collapsed_406_);
v___y_422_ = v___y_435_;
v___y_423_ = v_m_444_;
v_data_424_ = v_data_449_;
goto v___jp_421_;
}
}
}
}
v___jp_454_:
{
lean_object* v_ref_455_; lean_object* v___x_456_; 
v_ref_455_ = lean_ctor_get(v___y_413_, 5);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
lean_inc(v_fst_416_);
v___x_456_ = lean_apply_4(v_msg_411_, v_fst_416_, v___y_413_, v___y_414_, lean_box(0));
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___y_435_ = v_ref_455_;
v_a_436_ = v_a_457_;
goto v___jp_434_;
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v___x_456_);
v___x_458_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___closed__3);
v___y_435_ = v_ref_455_;
v_a_436_ = v___x_458_;
goto v___jp_434_;
}
}
v___jp_459_:
{
if (v_clsEnabled_409_ == 0)
{
if (v___y_460_ == 0)
{
lean_object* v___x_461_; lean_object* v_traceState_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_cache_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_489_; 
lean_del_object(v___x_430_);
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
lean_del_object(v___x_419_);
lean_dec_ref(v_msg_411_);
lean_dec_ref(v_tag_407_);
lean_dec(v_cls_405_);
v___x_461_ = lean_st_ref_take(v___y_414_);
v_traceState_462_ = lean_ctor_get(v___x_461_, 4);
v_env_463_ = lean_ctor_get(v___x_461_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_461_, 1);
v_ngen_465_ = lean_ctor_get(v___x_461_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_461_, 3);
v_cache_467_ = lean_ctor_get(v___x_461_, 5);
v_messages_468_ = lean_ctor_get(v___x_461_, 6);
v_infoState_469_ = lean_ctor_get(v___x_461_, 7);
v_snapshotTasks_470_ = lean_ctor_get(v___x_461_, 8);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_489_ == 0)
{
v___x_472_ = v___x_461_;
v_isShared_473_ = v_isSharedCheck_489_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_cache_467_);
lean_inc(v_traceState_462_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_461_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_489_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint64_t v_tid_474_; lean_object* v_traces_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_488_; 
v_tid_474_ = lean_ctor_get_uint64(v_traceState_462_, sizeof(void*)*1);
v_traces_475_ = lean_ctor_get(v_traceState_462_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_traceState_462_);
if (v_isSharedCheck_488_ == 0)
{
v___x_477_ = v_traceState_462_;
v_isShared_478_ = v_isSharedCheck_488_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_traces_475_);
lean_dec(v_traceState_462_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_488_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_410_, v_traces_475_);
lean_dec_ref(v_traces_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_479_);
lean_ctor_set_uint64(v_reuseFailAlloc_487_, sizeof(void*)*1, v_tid_474_);
v___x_481_ = v_reuseFailAlloc_487_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 4, v___x_481_);
v___x_483_ = v___x_472_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_env_463_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_cache_467_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_snapshotTasks_470_);
v___x_483_ = v_reuseFailAlloc_486_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_st_ref_set(v___y_414_, v___x_483_);
v___x_485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_fst_416_);
return v___x_485_;
}
}
}
}
}
else
{
goto v___jp_454_;
}
}
else
{
goto v___jp_454_;
}
}
v___jp_490_:
{
double v___x_492_; double v___x_493_; double v___x_494_; uint8_t v___x_495_; 
v___x_492_ = lean_unbox_float(v_snd_428_);
v___x_493_ = lean_unbox_float(v_fst_427_);
v___x_494_ = lean_float_sub(v___x_492_, v___x_493_);
v___x_495_ = lean_float_decLt(v___y_491_, v___x_494_);
v___y_460_ = v___x_495_;
goto v___jp_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7___boxed(lean_object* v_cls_508_, lean_object* v_collapsed_509_, lean_object* v_tag_510_, lean_object* v_opts_511_, lean_object* v_clsEnabled_512_, lean_object* v_oldTraces_513_, lean_object* v_msg_514_, lean_object* v_resStartStop_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
uint8_t v_collapsed_boxed_519_; uint8_t v_clsEnabled_boxed_520_; lean_object* v_res_521_; 
v_collapsed_boxed_519_ = lean_unbox(v_collapsed_509_);
v_clsEnabled_boxed_520_ = lean_unbox(v_clsEnabled_512_);
v_res_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v_cls_508_, v_collapsed_boxed_519_, v_tag_510_, v_opts_511_, v_clsEnabled_boxed_520_, v_oldTraces_513_, v_msg_514_, v_resStartStop_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_opts_511_);
return v_res_521_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_522_; double v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1000000000u);
v___x_523_ = lean_float_of_nat(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_556_, lean_object* v_s_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v_a_572_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; uint8_t v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v_a_592_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v_a_605_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v_a_632_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v_a_655_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v_a_668_; lean_object* v___y_671_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v_element_763_; lean_object* v_children_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_997_; 
v_element_763_ = lean_ctor_get(v_s_557_, 0);
v_children_764_ = lean_ctor_get(v_s_557_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_s_557_);
if (v_isSharedCheck_997_ == 0)
{
v___x_766_ = v_s_557_;
v_isShared_767_ = v_isSharedCheck_997_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_children_764_);
lean_inc(v_element_763_);
lean_dec(v_s_557_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_997_;
goto v_resetjp_765_;
}
v___jp_561_:
{
lean_object* v___x_573_; double v___x_574_; double v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_573_ = lean_io_get_num_heartbeats();
v___x_574_ = lean_float_of_nat(v___y_568_);
v___x_575_ = lean_float_of_nat(v___x_573_);
v___x_576_ = lean_box_float(v___x_574_);
v___x_577_ = lean_box_float(v___x_575_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_572_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v___y_567_, v___y_565_, v___y_570_, v___y_566_, v___y_563_, v___y_569_, v___y_562_, v___x_579_, v___y_564_, v___y_571_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_566_);
return v___x_580_;
}
v___jp_581_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_a_592_);
v___y_562_ = v___y_582_;
v___y_563_ = v___y_583_;
v___y_564_ = v___y_584_;
v___y_565_ = v___y_585_;
v___y_566_ = v___y_586_;
v___y_567_ = v___y_588_;
v___y_568_ = v___y_587_;
v___y_569_ = v___y_590_;
v___y_570_ = v___y_589_;
v___y_571_ = v___y_591_;
v_a_572_ = v___x_593_;
goto v___jp_561_;
}
v___jp_594_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_a_605_);
v___y_562_ = v___y_595_;
v___y_563_ = v___y_596_;
v___y_564_ = v___y_597_;
v___y_565_ = v___y_598_;
v___y_566_ = v___y_599_;
v___y_567_ = v___y_601_;
v___y_568_ = v___y_600_;
v___y_569_ = v___y_603_;
v___y_570_ = v___y_602_;
v___y_571_ = v___y_604_;
v_a_572_ = v___x_606_;
goto v___jp_561_;
}
v___jp_607_:
{
if (lean_obj_tag(v___y_618_) == 0)
{
lean_object* v_a_619_; 
v_a_619_ = lean_ctor_get(v___y_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___y_618_);
v___y_582_ = v___y_608_;
v___y_583_ = v___y_609_;
v___y_584_ = v___y_610_;
v___y_585_ = v___y_611_;
v___y_586_ = v___y_612_;
v___y_587_ = v___y_614_;
v___y_588_ = v___y_613_;
v___y_589_ = v___y_616_;
v___y_590_ = v___y_615_;
v___y_591_ = v___y_617_;
v_a_592_ = v_a_619_;
goto v___jp_581_;
}
else
{
lean_object* v_a_620_; 
v_a_620_ = lean_ctor_get(v___y_618_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___y_618_);
v___y_595_ = v___y_608_;
v___y_596_ = v___y_609_;
v___y_597_ = v___y_610_;
v___y_598_ = v___y_611_;
v___y_599_ = v___y_612_;
v___y_600_ = v___y_614_;
v___y_601_ = v___y_613_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_615_;
v___y_604_ = v___y_617_;
v_a_605_ = v_a_620_;
goto v___jp_594_;
}
}
v___jp_621_:
{
lean_object* v___x_633_; double v___x_634_; double v___x_635_; double v___x_636_; double v___x_637_; double v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_633_ = lean_io_mono_nanos_now();
v___x_634_ = lean_float_of_nat(v___y_623_);
v___x_635_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_636_ = lean_float_div(v___x_634_, v___x_635_);
v___x_637_ = lean_float_of_nat(v___x_633_);
v___x_638_ = lean_float_div(v___x_637_, v___x_635_);
v___x_639_ = lean_box_float(v___x_636_);
v___x_640_ = lean_box_float(v___x_638_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_632_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7(v___y_628_, v___y_626_, v___y_630_, v___y_627_, v___y_624_, v___y_629_, v___y_622_, v___x_642_, v___y_625_, v___y_631_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v___y_627_);
return v___x_643_;
}
v___jp_644_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v_a_655_);
v___y_622_ = v___y_645_;
v___y_623_ = v___y_646_;
v___y_624_ = v___y_647_;
v___y_625_ = v___y_648_;
v___y_626_ = v___y_649_;
v___y_627_ = v___y_650_;
v___y_628_ = v___y_651_;
v___y_629_ = v___y_653_;
v___y_630_ = v___y_652_;
v___y_631_ = v___y_654_;
v_a_632_ = v___x_656_;
goto v___jp_621_;
}
v___jp_657_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_a_668_);
v___y_622_ = v___y_658_;
v___y_623_ = v___y_659_;
v___y_624_ = v___y_660_;
v___y_625_ = v___y_661_;
v___y_626_ = v___y_662_;
v___y_627_ = v___y_663_;
v___y_628_ = v___y_664_;
v___y_629_ = v___y_666_;
v___y_630_ = v___y_665_;
v___y_631_ = v___y_667_;
v_a_632_ = v___x_669_;
goto v___jp_621_;
}
v___jp_670_:
{
if (lean_obj_tag(v___y_681_) == 0)
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v___y_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___y_681_);
v___y_645_ = v___y_671_;
v___y_646_ = v___y_672_;
v___y_647_ = v___y_673_;
v___y_648_ = v___y_674_;
v___y_649_ = v___y_675_;
v___y_650_ = v___y_676_;
v___y_651_ = v___y_677_;
v___y_652_ = v___y_679_;
v___y_653_ = v___y_678_;
v___y_654_ = v___y_680_;
v_a_655_ = v_a_682_;
goto v___jp_644_;
}
else
{
lean_object* v_a_683_; 
v_a_683_ = lean_ctor_get(v___y_681_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v___y_681_);
v___y_658_ = v___y_671_;
v___y_659_ = v___y_672_;
v___y_660_ = v___y_673_;
v___y_661_ = v___y_674_;
v___y_662_ = v___y_675_;
v___y_663_ = v___y_676_;
v___y_664_ = v___y_677_;
v___y_665_ = v___y_679_;
v___y_666_ = v___y_678_;
v___y_667_ = v___y_680_;
v_a_668_ = v_a_683_;
goto v___jp_657_;
}
}
v___jp_684_:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___redArg(v___y_689_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_699_ = l_Lean_trace_profiler_useHeartbeats;
v___x_700_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_695_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_io_mono_nanos_now();
v___x_702_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_692_, v___y_693_, v___y_689_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref(v___x_702_);
if (lean_obj_tag(v___y_690_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_val_703_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v___y_690_);
v___x_704_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
v___x_705_ = l_Lean_Name_mkStr2(v___y_694_, v___x_704_);
lean_inc(v___x_705_);
v___x_706_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_705_, v___y_693_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; uint8_t v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v___x_708_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v___x_705_);
lean_dec(v_val_703_);
lean_dec(v___y_687_);
v___x_709_ = lean_box(0);
v___y_645_ = v___y_691_;
v___y_646_ = v___x_701_;
v___y_647_ = v___y_685_;
v___y_648_ = v___y_693_;
v___y_649_ = v___y_686_;
v___y_650_ = v___y_695_;
v___y_651_ = v___y_696_;
v___y_652_ = v___y_688_;
v___y_653_ = v_a_698_;
v___y_654_ = v___y_689_;
v_a_655_ = v___x_709_;
goto v___jp_644_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Lean_Elab_InfoTree_format(v_val_703_, v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v___y_687_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l_Lean_MessageData_ofFormat(v_a_712_);
v___x_714_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_705_, v___x_713_, v___y_693_, v___y_689_);
v___y_671_ = v___y_691_;
v___y_672_ = v___x_701_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_693_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_695_;
v___y_677_ = v___y_696_;
v___y_678_ = v_a_698_;
v___y_679_ = v___y_688_;
v___y_680_ = v___y_689_;
v___y_681_ = v___x_714_;
goto v___jp_670_;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_725_; 
lean_dec(v___x_705_);
v_a_715_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_725_ == 0)
{
v___x_717_ = v___x_711_;
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_711_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_725_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_io_error_to_string(v_a_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 3);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_724_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = l_Lean_MessageData_ofFormat(v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_687_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___y_658_ = v___y_691_;
v___y_659_ = v___x_701_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_693_;
v___y_662_ = v___y_686_;
v___y_663_ = v___y_695_;
v___y_664_ = v___y_696_;
v___y_665_ = v___y_688_;
v___y_666_ = v_a_698_;
v___y_667_ = v___y_689_;
v_a_668_ = v___x_723_;
goto v___jp_657_;
}
}
}
}
}
else
{
lean_object* v_a_726_; 
lean_dec(v___x_705_);
lean_dec(v_val_703_);
lean_dec(v___y_687_);
v_a_726_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_706_);
v___y_658_ = v___y_691_;
v___y_659_ = v___x_701_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_693_;
v___y_662_ = v___y_686_;
v___y_663_ = v___y_695_;
v___y_664_ = v___y_696_;
v___y_665_ = v___y_688_;
v___y_666_ = v_a_698_;
v___y_667_ = v___y_689_;
v_a_668_ = v_a_726_;
goto v___jp_657_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec_ref(v___y_694_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
v___x_727_ = lean_box(0);
v___y_645_ = v___y_691_;
v___y_646_ = v___x_701_;
v___y_647_ = v___y_685_;
v___y_648_ = v___y_693_;
v___y_649_ = v___y_686_;
v___y_650_ = v___y_695_;
v___y_651_ = v___y_696_;
v___y_652_ = v___y_688_;
v___y_653_ = v_a_698_;
v___y_654_ = v___y_689_;
v_a_655_ = v___x_727_;
goto v___jp_644_;
}
}
else
{
lean_dec_ref(v___y_694_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
v___y_671_ = v___y_691_;
v___y_672_ = v___x_701_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_693_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_695_;
v___y_677_ = v___y_696_;
v___y_678_ = v_a_698_;
v___y_679_ = v___y_688_;
v___y_680_ = v___y_689_;
v___y_681_ = v___x_702_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_io_get_num_heartbeats();
v___x_729_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_692_, v___y_693_, v___y_689_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref(v___x_729_);
if (lean_obj_tag(v___y_690_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_val_730_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_val_730_);
lean_dec_ref(v___y_690_);
v___x_731_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
v___x_732_ = l_Lean_Name_mkStr2(v___y_694_, v___x_731_);
lean_inc(v___x_732_);
v___x_733_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_732_, v___y_693_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v___x_732_);
lean_dec(v_val_730_);
lean_dec(v___y_687_);
v___x_736_ = lean_box(0);
v___y_582_ = v___y_691_;
v___y_583_ = v___y_685_;
v___y_584_ = v___y_693_;
v___y_585_ = v___y_686_;
v___y_586_ = v___y_695_;
v___y_587_ = v___x_728_;
v___y_588_ = v___y_696_;
v___y_589_ = v___y_688_;
v___y_590_ = v_a_698_;
v___y_591_ = v___y_689_;
v_a_592_ = v___x_736_;
goto v___jp_581_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(0);
v___x_738_ = l_Lean_Elab_InfoTree_format(v_val_730_, v___x_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v___y_687_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_MessageData_ofFormat(v_a_739_);
v___x_741_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_732_, v___x_740_, v___y_693_, v___y_689_);
v___y_608_ = v___y_691_;
v___y_609_ = v___y_685_;
v___y_610_ = v___y_693_;
v___y_611_ = v___y_686_;
v___y_612_ = v___y_695_;
v___y_613_ = v___y_696_;
v___y_614_ = v___x_728_;
v___y_615_ = v_a_698_;
v___y_616_ = v___y_688_;
v___y_617_ = v___y_689_;
v___y_618_ = v___x_741_;
goto v___jp_607_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_732_);
v_a_742_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_752_ == 0)
{
v___x_744_ = v___x_738_;
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_io_error_to_string(v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 3);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_751_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = l_Lean_MessageData_ofFormat(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_687_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___y_595_ = v___y_691_;
v___y_596_ = v___y_685_;
v___y_597_ = v___y_693_;
v___y_598_ = v___y_686_;
v___y_599_ = v___y_695_;
v___y_600_ = v___x_728_;
v___y_601_ = v___y_696_;
v___y_602_ = v___y_688_;
v___y_603_ = v_a_698_;
v___y_604_ = v___y_689_;
v_a_605_ = v___x_750_;
goto v___jp_594_;
}
}
}
}
}
else
{
lean_object* v_a_753_; 
lean_dec(v___x_732_);
lean_dec(v_val_730_);
lean_dec(v___y_687_);
v_a_753_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_733_);
v___y_595_ = v___y_691_;
v___y_596_ = v___y_685_;
v___y_597_ = v___y_693_;
v___y_598_ = v___y_686_;
v___y_599_ = v___y_695_;
v___y_600_ = v___x_728_;
v___y_601_ = v___y_696_;
v___y_602_ = v___y_688_;
v___y_603_ = v_a_698_;
v___y_604_ = v___y_689_;
v_a_605_ = v_a_753_;
goto v___jp_594_;
}
}
else
{
lean_object* v___x_754_; 
lean_dec_ref(v___y_694_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
v___x_754_ = lean_box(0);
v___y_582_ = v___y_691_;
v___y_583_ = v___y_685_;
v___y_584_ = v___y_693_;
v___y_585_ = v___y_686_;
v___y_586_ = v___y_695_;
v___y_587_ = v___x_728_;
v___y_588_ = v___y_696_;
v___y_589_ = v___y_688_;
v___y_590_ = v_a_698_;
v___y_591_ = v___y_689_;
v_a_592_ = v___x_754_;
goto v___jp_581_;
}
}
else
{
lean_dec_ref(v___y_694_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
v___y_608_ = v___y_691_;
v___y_609_ = v___y_685_;
v___y_610_ = v___y_693_;
v___y_611_ = v___y_686_;
v___y_612_ = v___y_695_;
v___y_613_ = v___y_696_;
v___y_614_ = v___x_728_;
v___y_615_ = v_a_698_;
v___y_616_ = v___y_688_;
v___y_617_ = v___y_689_;
v___y_618_ = v___x_729_;
goto v___jp_607_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
v_a_755_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_697_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_697_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
v_resetjp_765_:
{
lean_object* v_desc_768_; lean_object* v_diagnostics_769_; lean_object* v_infoTree_x3f_770_; lean_object* v_desc_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___x_933_; 
v_desc_768_ = lean_ctor_get(v_element_763_, 0);
lean_inc_ref(v_desc_768_);
v_diagnostics_769_ = lean_ctor_get(v_element_763_, 1);
lean_inc_ref(v_diagnostics_769_);
v_infoTree_x3f_770_ = lean_ctor_get(v_element_763_, 2);
lean_inc(v_infoTree_x3f_770_);
lean_dec_ref(v_element_763_);
v___x_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_933_, 0, v_desc_768_);
switch(lean_obj_tag(v_range_x3f_556_))
{
case 0:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9));
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v_desc_772_ = v___x_935_;
v___y_773_ = v_a_558_;
v___y_774_ = v_a_559_;
goto v___jp_771_;
}
case 1:
{
lean_object* v_range_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_994_; 
v_range_936_ = lean_ctor_get(v_range_x3f_556_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_range_x3f_556_);
if (v_isSharedCheck_994_ == 0)
{
v___x_938_ = v_range_x3f_556_;
v_isShared_939_ = v_isSharedCheck_994_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_range_936_);
lean_dec(v_range_x3f_556_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_994_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_fileMap_940_; lean_object* v_start_941_; lean_object* v_stop_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_993_; 
v_fileMap_940_ = lean_ctor_get(v_a_558_, 1);
v_start_941_ = lean_ctor_get(v_range_936_, 0);
v_stop_942_ = lean_ctor_get(v_range_936_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_range_936_);
if (v_isSharedCheck_993_ == 0)
{
v___x_944_ = v_range_936_;
v_isShared_945_ = v_isSharedCheck_993_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_stop_942_);
lean_inc(v_start_941_);
lean_dec(v_range_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_993_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v_line_947_; lean_object* v_column_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_992_; 
lean_inc_ref(v_fileMap_940_);
v___x_946_ = l_Lean_FileMap_toPosition(v_fileMap_940_, v_start_941_);
lean_dec(v_start_941_);
v_line_947_ = lean_ctor_get(v___x_946_, 0);
v_column_948_ = lean_ctor_get(v___x_946_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_992_ == 0)
{
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_992_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_column_948_);
lean_inc(v_line_947_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_992_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v_line_953_; lean_object* v_column_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_991_; 
lean_inc_ref(v_fileMap_940_);
v___x_952_ = l_Lean_FileMap_toPosition(v_fileMap_940_, v_stop_942_);
lean_dec(v_stop_942_);
v_line_953_ = lean_ctor_get(v___x_952_, 0);
v_column_954_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_991_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_991_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_column_954_);
lean_inc(v_line_953_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_991_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11));
v___x_959_ = l_Nat_reprFast(v_line_947_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 3);
lean_ctor_set(v___x_938_, 0, v___x_959_);
v___x_961_ = v___x_938_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_990_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 5);
lean_ctor_set(v___x_956_, 1, v___x_961_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_989_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 5);
lean_ctor_set(v___x_950_, 1, v___x_964_);
lean_ctor_set(v___x_950_, 0, v___x_963_);
v___x_966_ = v___x_950_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_988_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = l_Nat_reprFast(v_column_948_);
v___x_968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 5);
lean_ctor_set(v___x_944_, 1, v___x_968_);
lean_ctor_set(v___x_944_, 0, v___x_966_);
v___x_970_ = v___x_944_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_987_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Nat_reprFast(v_line_953_);
v___x_976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_958_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_964_);
v___x_979_ = l_Nat_reprFast(v_column_954_);
v___x_980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_971_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_974_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__18));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_933_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v_desc_772_ = v___x_986_;
v___y_773_ = v_a_558_;
v___y_774_ = v_a_559_;
goto v___jp_771_;
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
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__20));
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_933_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v_desc_772_ = v___x_996_;
v___y_773_ = v_a_558_;
v___y_774_ = v_a_559_;
goto v___jp_771_;
}
}
v___jp_771_:
{
lean_object* v_msgLog_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_931_; 
v_msgLog_775_ = lean_ctor_get(v_diagnostics_769_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_diagnostics_769_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_diagnostics_769_, 1);
lean_dec(v_unused_932_);
v___x_777_ = v_diagnostics_769_;
v_isShared_778_ = v_isSharedCheck_931_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_msgLog_775_);
lean_dec(v_diagnostics_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_931_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_MessageLog_toList(v_msgLog_775_);
lean_dec_ref(v_msgLog_775_);
v___x_780_ = lean_box(0);
v___x_781_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_779_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_options_782_; lean_object* v_a_783_; lean_object* v_ref_784_; uint8_t v_hasTrace_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_options_782_ = lean_ctor_get(v___y_773_, 2);
v_a_783_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_781_);
v_ref_784_ = lean_ctor_get(v___y_773_, 5);
v_hasTrace_785_ = lean_ctor_get_uint8(v_options_782_, sizeof(void*)*1);
v___x_786_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__2));
v___x_787_ = lean_array_to_list(v_children_764_);
if (v_hasTrace_785_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_a_783_);
lean_dec(v_desc_772_);
lean_del_object(v___x_766_);
v___x_788_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_787_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_788_, 0);
lean_dec(v_unused_843_);
v___x_790_ = v___x_788_;
v_isShared_791_ = v_isSharedCheck_842_;
goto v_resetjp_789_;
}
else
{
lean_dec(v___x_788_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_842_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
if (lean_obj_tag(v_infoTree_x3f_770_) == 1)
{
lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_837_; 
lean_del_object(v___x_790_);
v_val_792_ = lean_ctor_get(v_infoTree_x3f_770_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_infoTree_x3f_770_);
if (v_isSharedCheck_837_ == 0)
{
v___x_794_ = v_infoTree_x3f_770_;
v_isShared_795_ = v_isSharedCheck_837_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v_infoTree_x3f_770_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_837_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_797_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_796_, v___y_773_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_828_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_828_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_del_object(v___x_794_);
lean_dec(v_val_792_);
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
v___x_803_ = lean_box(0);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_803_);
v___x_805_ = v___x_800_;
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
lean_del_object(v___x_800_);
v___x_807_ = lean_box(0);
v___x_808_ = l_Lean_Elab_InfoTree_format(v_val_792_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_794_);
lean_del_object(v___x_777_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_MessageData_ofFormat(v_a_809_);
v___x_811_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_796_, v___x_810_, v___y_773_, v___y_774_);
lean_dec_ref(v___y_773_);
return v___x_811_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_827_; 
lean_inc(v_ref_784_);
lean_dec_ref(v___y_773_);
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
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 3);
lean_ctor_set(v___x_794_, 0, v___x_816_);
v___x_818_ = v___x_794_;
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
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_819_);
lean_ctor_set(v___x_777_, 0, v_ref_784_);
v___x_821_ = v___x_777_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_ref_784_);
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
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_del_object(v___x_794_);
lean_dec(v_val_792_);
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
v_a_829_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_797_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_797_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
lean_dec(v_infoTree_x3f_770_);
v___x_838_ = lean_box(0);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_838_);
v___x_840_ = v___x_790_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
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
else
{
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
lean_dec(v_infoTree_x3f_770_);
return v___x_788_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__5));
v___x_845_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_844_, v___y_773_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__7));
v___x_848_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___x_847_, v_a_783_);
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 5);
lean_ctor_set(v___x_777_, 1, v___x_848_);
lean_ctor_set(v___x_777_, 0, v_desc_772_);
v___x_850_ = v___x_777_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_desc_772_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_914_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___f_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___f_851_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_851_, 0, v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___closed__1));
v___x_853_ = lean_unbox(v_a_846_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = l_Lean_trace_profiler;
v___x_855_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_options_782_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v___f_851_);
lean_dec(v_a_846_);
v___x_856_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_787_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_910_; 
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_856_, 0);
lean_dec(v_unused_911_);
v___x_858_ = v___x_856_;
v_isShared_859_ = v_isSharedCheck_910_;
goto v_resetjp_857_;
}
else
{
lean_dec(v___x_856_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_910_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_infoTree_x3f_770_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_858_);
v_val_860_ = lean_ctor_get(v_infoTree_x3f_770_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_infoTree_x3f_770_);
if (v_isSharedCheck_905_ == 0)
{
v___x_862_ = v_infoTree_x3f_770_;
v_isShared_863_ = v_isSharedCheck_905_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_val_860_);
lean_dec(v_infoTree_x3f_770_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_905_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_865_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___x_864_, v___y_773_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_896_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_896_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_896_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_896_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
v___x_870_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_del_object(v___x_862_);
lean_dec(v_val_860_);
lean_dec_ref(v___y_773_);
lean_del_object(v___x_766_);
v___x_871_ = lean_box(0);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_868_);
v___x_875_ = lean_box(0);
v___x_876_ = l_Lean_Elab_InfoTree_format(v_val_860_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_862_);
lean_del_object(v___x_766_);
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = l_Lean_MessageData_ofFormat(v_a_877_);
v___x_879_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_864_, v___x_878_, v___y_773_, v___y_774_);
lean_dec_ref(v___y_773_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_895_; 
lean_inc(v_ref_784_);
lean_dec_ref(v___y_773_);
v_a_880_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_882_ = v___x_876_;
v_isShared_883_ = v_isSharedCheck_895_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_876_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_895_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_io_error_to_string(v_a_880_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 3);
lean_ctor_set(v___x_862_, 0, v___x_884_);
v___x_886_ = v___x_862_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_894_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_MessageData_ofFormat(v___x_886_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_887_);
lean_ctor_set(v___x_766_, 0, v_ref_784_);
v___x_889_ = v___x_766_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_ref_784_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_889_);
v___x_891_ = v___x_882_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
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
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_862_);
lean_dec(v_val_860_);
lean_dec_ref(v___y_773_);
lean_del_object(v___x_766_);
v_a_897_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_865_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_865_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_dec_ref(v___y_773_);
lean_dec(v_infoTree_x3f_770_);
lean_del_object(v___x_766_);
v___x_906_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_906_);
v___x_908_ = v___x_858_;
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
lean_dec_ref(v___y_773_);
lean_dec(v_infoTree_x3f_770_);
lean_del_object(v___x_766_);
return v___x_856_;
}
}
else
{
uint8_t v___x_912_; 
lean_inc(v_ref_784_);
lean_inc_ref(v_options_782_);
lean_del_object(v___x_766_);
v___x_912_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
v___y_685_ = v___x_912_;
v___y_686_ = v_hasTrace_785_;
v___y_687_ = v_ref_784_;
v___y_688_ = v___x_852_;
v___y_689_ = v___y_774_;
v___y_690_ = v_infoTree_x3f_770_;
v___y_691_ = v___f_851_;
v___y_692_ = v___x_787_;
v___y_693_ = v___y_773_;
v___y_694_ = v___x_786_;
v___y_695_ = v_options_782_;
v___y_696_ = v___x_844_;
goto v___jp_684_;
}
}
else
{
uint8_t v___x_913_; 
lean_inc(v_ref_784_);
lean_inc_ref(v_options_782_);
lean_del_object(v___x_766_);
v___x_913_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
v___y_685_ = v___x_913_;
v___y_686_ = v_hasTrace_785_;
v___y_687_ = v_ref_784_;
v___y_688_ = v___x_852_;
v___y_689_ = v___y_774_;
v___y_690_ = v_infoTree_x3f_770_;
v___y_691_ = v___f_851_;
v___y_692_ = v___x_787_;
v___y_693_ = v___y_773_;
v___y_694_ = v___x_786_;
v___y_695_ = v_options_782_;
v___y_696_ = v___x_844_;
goto v___jp_684_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___x_787_);
lean_dec(v_a_783_);
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
lean_dec(v_desc_772_);
lean_dec(v_infoTree_x3f_770_);
lean_del_object(v___x_766_);
v_a_915_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_845_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_845_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_777_);
lean_dec_ref(v___y_773_);
lean_dec(v_desc_772_);
lean_dec(v_infoTree_x3f_770_);
lean_del_object(v___x_766_);
lean_dec_ref(v_children_764_);
v_a_923_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_781_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_781_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
if (lean_obj_tag(v_as_998_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_head_1004_; lean_object* v_tail_1005_; lean_object* v_reportingRange_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_head_1004_ = lean_ctor_get(v_as_998_, 0);
lean_inc(v_head_1004_);
v_tail_1005_ = lean_ctor_get(v_as_998_, 1);
lean_inc(v_tail_1005_);
lean_dec_ref(v_as_998_);
v_reportingRange_1006_ = lean_ctor_get(v_head_1004_, 1);
lean_inc(v_reportingRange_1006_);
v___x_1007_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_1004_);
lean_inc_ref(v___y_999_);
v___x_1008_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_1006_, v___x_1007_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_dec_ref(v___x_1008_);
v_as_998_ = v_tail_1005_;
goto _start;
}
else
{
lean_dec(v_tail_1005_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_1015_, lean_object* v_s_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_1015_, v_s_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_1021_, v_x_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_1027_, v_x_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11(lean_object* v_00_u03b1_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___redArg(v_x_1034_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__7_spec__11(v_00_u03b1_1039_, v_x_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_box(2);
lean_inc_ref(v_a_1046_);
v___x_1050_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_1049_, v_s_1045_, v_a_1046_, v_a_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Language_SnapshotTree_trace(v_s_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1055_;
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

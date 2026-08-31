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
v___x_37_ = lean_st_ref_put(v___y_10_, v___x_36_);
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
lean_dec_ref_known(v___x_60_, 1);
if (lean_obj_tag(v_val_62_) == 1)
{
uint8_t v_v_63_; 
v_v_63_ = lean_ctor_get_uint8(v_val_62_, 0);
lean_dec_ref_known(v_val_62_, 0);
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
v___x_87_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_87_, 10, v___x_85_);
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
v_options_107_ = lean_ctor_get(v___y_102_, 1);
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
v_ref_128_ = lean_ctor_get(v___y_125_, 4);
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
v___x_165_ = lean_st_ref_put(v___y_126_, v___x_164_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_233_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_a_241_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v_x_231_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v_x_231_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 0);
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_252_, lean_object* v_opt_253_){
_start:
{
lean_object* v_name_254_; lean_object* v_defValue_255_; lean_object* v_map_256_; lean_object* v___x_257_; 
v_name_254_ = lean_ctor_get(v_opt_253_, 0);
v_defValue_255_ = lean_ctor_get(v_opt_253_, 1);
v_map_256_ = lean_ctor_get(v_opts_252_, 0);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_256_, v_name_254_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_inc(v_defValue_255_);
return v_defValue_255_;
}
else
{
lean_object* v_val_258_; 
v_val_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_val_258_);
lean_dec_ref_known(v___x_257_, 1);
if (lean_obj_tag(v_val_258_) == 3)
{
lean_object* v_v_259_; 
v_v_259_ = lean_ctor_get(v_val_258_, 0);
lean_inc(v_v_259_);
lean_dec_ref_known(v_val_258_, 1);
return v_v_259_;
}
else
{
lean_dec(v_val_258_);
lean_inc(v_defValue_255_);
return v_defValue_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_260_, lean_object* v_opt_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_260_, v_opt_261_);
lean_dec_ref(v_opt_261_);
lean_dec_ref(v_opts_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_263_, size_t v_i_264_, lean_object* v_bs_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_266_ == 0)
{
return v_bs_265_;
}
else
{
lean_object* v_v_267_; lean_object* v_msg_268_; lean_object* v___x_269_; lean_object* v_bs_x27_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v_v_267_ = lean_array_uget_borrowed(v_bs_265_, v_i_264_);
v_msg_268_ = lean_ctor_get(v_v_267_, 1);
lean_inc_ref(v_msg_268_);
v___x_269_ = lean_unsigned_to_nat(0u);
v_bs_x27_270_ = lean_array_uset(v_bs_265_, v_i_264_, v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_264_, v___x_271_);
v___x_273_ = lean_array_uset(v_bs_x27_270_, v_i_264_, v_msg_268_);
v_i_264_ = v___x_272_;
v_bs_265_ = v___x_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_bs_277_){
_start:
{
size_t v_sz_boxed_278_; size_t v_i_boxed_279_; lean_object* v_res_280_; 
v_sz_boxed_278_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_279_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_278_, v_i_boxed_279_, v_bs_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_281_, lean_object* v_data_282_, lean_object* v_ref_283_, lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_toCold_288_; lean_object* v_options_289_; lean_object* v_currRecDepth_290_; lean_object* v_maxRecDepth_291_; lean_object* v_ref_292_; lean_object* v_currNamespace_293_; lean_object* v_openDecls_294_; lean_object* v_initHeartbeats_295_; lean_object* v_maxHeartbeats_296_; lean_object* v_currMacroScope_297_; uint8_t v_diag_298_; uint8_t v_suppressElabErrors_299_; lean_object* v___x_300_; lean_object* v_traceState_301_; lean_object* v_traces_302_; lean_object* v_ref_303_; lean_object* v___x_304_; lean_object* v___x_305_; size_t v_sz_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v_msg_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_348_; 
v_toCold_288_ = lean_ctor_get(v___y_285_, 0);
v_options_289_ = lean_ctor_get(v___y_285_, 1);
v_currRecDepth_290_ = lean_ctor_get(v___y_285_, 2);
v_maxRecDepth_291_ = lean_ctor_get(v___y_285_, 3);
v_ref_292_ = lean_ctor_get(v___y_285_, 4);
v_currNamespace_293_ = lean_ctor_get(v___y_285_, 5);
v_openDecls_294_ = lean_ctor_get(v___y_285_, 6);
v_initHeartbeats_295_ = lean_ctor_get(v___y_285_, 7);
v_maxHeartbeats_296_ = lean_ctor_get(v___y_285_, 8);
v_currMacroScope_297_ = lean_ctor_get(v___y_285_, 9);
v_diag_298_ = lean_ctor_get_uint8(v___y_285_, sizeof(void*)*10);
v_suppressElabErrors_299_ = lean_ctor_get_uint8(v___y_285_, sizeof(void*)*10 + 1);
v___x_300_ = lean_st_ref_get(v___y_286_);
v_traceState_301_ = lean_ctor_get(v___x_300_, 4);
lean_inc_ref(v_traceState_301_);
lean_dec(v___x_300_);
v_traces_302_ = lean_ctor_get(v_traceState_301_, 0);
lean_inc_ref(v_traces_302_);
lean_dec_ref(v_traceState_301_);
v_ref_303_ = l_Lean_replaceRef(v_ref_283_, v_ref_292_);
lean_inc(v_currMacroScope_297_);
lean_inc(v_maxHeartbeats_296_);
lean_inc(v_initHeartbeats_295_);
lean_inc(v_openDecls_294_);
lean_inc(v_currNamespace_293_);
lean_inc(v_maxRecDepth_291_);
lean_inc(v_currRecDepth_290_);
lean_inc_ref(v_options_289_);
lean_inc_ref(v_toCold_288_);
v___x_304_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_304_, 0, v_toCold_288_);
lean_ctor_set(v___x_304_, 1, v_options_289_);
lean_ctor_set(v___x_304_, 2, v_currRecDepth_290_);
lean_ctor_set(v___x_304_, 3, v_maxRecDepth_291_);
lean_ctor_set(v___x_304_, 4, v_ref_303_);
lean_ctor_set(v___x_304_, 5, v_currNamespace_293_);
lean_ctor_set(v___x_304_, 6, v_openDecls_294_);
lean_ctor_set(v___x_304_, 7, v_initHeartbeats_295_);
lean_ctor_set(v___x_304_, 8, v_maxHeartbeats_296_);
lean_ctor_set(v___x_304_, 9, v_currMacroScope_297_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*10, v_diag_298_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*10 + 1, v_suppressElabErrors_299_);
v___x_305_ = l_Lean_PersistentArray_toArray___redArg(v_traces_302_);
lean_dec_ref(v_traces_302_);
v_sz_306_ = lean_array_size(v___x_305_);
v___x_307_ = ((size_t)0ULL);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_306_, v___x_307_, v___x_305_);
v_msg_309_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_309_, 0, v_data_282_);
lean_ctor_set(v_msg_309_, 1, v_msg_284_);
lean_ctor_set(v_msg_309_, 2, v___x_308_);
v___x_310_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_309_, v___x_304_, v___y_286_);
lean_dec_ref_known(v___x_304_, 10);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_348_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_348_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_348_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v_traceState_316_; lean_object* v_env_317_; lean_object* v_nextMacroScope_318_; lean_object* v_ngen_319_; lean_object* v_auxDeclNGen_320_; lean_object* v_cache_321_; lean_object* v_messages_322_; lean_object* v_infoState_323_; lean_object* v_snapshotTasks_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_347_; 
v___x_315_ = lean_st_ref_take(v___y_286_);
v_traceState_316_ = lean_ctor_get(v___x_315_, 4);
v_env_317_ = lean_ctor_get(v___x_315_, 0);
v_nextMacroScope_318_ = lean_ctor_get(v___x_315_, 1);
v_ngen_319_ = lean_ctor_get(v___x_315_, 2);
v_auxDeclNGen_320_ = lean_ctor_get(v___x_315_, 3);
v_cache_321_ = lean_ctor_get(v___x_315_, 5);
v_messages_322_ = lean_ctor_get(v___x_315_, 6);
v_infoState_323_ = lean_ctor_get(v___x_315_, 7);
v_snapshotTasks_324_ = lean_ctor_get(v___x_315_, 8);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_347_ == 0)
{
v___x_326_ = v___x_315_;
v_isShared_327_ = v_isSharedCheck_347_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snapshotTasks_324_);
lean_inc(v_infoState_323_);
lean_inc(v_messages_322_);
lean_inc(v_cache_321_);
lean_inc(v_traceState_316_);
lean_inc(v_auxDeclNGen_320_);
lean_inc(v_ngen_319_);
lean_inc(v_nextMacroScope_318_);
lean_inc(v_env_317_);
lean_dec(v___x_315_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_347_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint64_t v_tid_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_345_; 
v_tid_328_ = lean_ctor_get_uint64(v_traceState_316_, sizeof(void*)*1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_traceState_316_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_traceState_316_, 0);
lean_dec(v_unused_346_);
v___x_330_ = v_traceState_316_;
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_traceState_316_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_ref_283_);
lean_ctor_set(v___x_332_, 1, v_a_311_);
v___x_333_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_281_, v___x_332_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_333_);
lean_ctor_set_uint64(v_reuseFailAlloc_344_, sizeof(void*)*1, v_tid_328_);
v___x_335_ = v_reuseFailAlloc_344_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 4, v___x_335_);
v___x_337_ = v___x_326_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_env_317_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_nextMacroScope_318_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_ngen_319_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_auxDeclNGen_320_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v_cache_321_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_messages_322_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v_snapshotTasks_324_);
v___x_337_ = v_reuseFailAlloc_343_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = lean_st_ref_put(v___y_286_, v___x_337_);
v___x_339_ = lean_box(0);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_339_);
v___x_341_ = v___x_313_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
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
lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v_data_384_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___y_392_; lean_object* v_a_393_; uint8_t v___y_408_; double v___y_439_; 
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
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = l_Lean_trace_profiler_useHeartbeats;
v___x_445_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_371_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; double v___x_448_; double v___x_449_; double v___x_450_; 
v___x_446_ = l_Lean_trace_profiler_threshold;
v___x_447_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_371_, v___x_446_);
v___x_448_ = lean_float_of_nat(v___x_447_);
v___x_449_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_450_ = lean_float_div(v___x_448_, v___x_449_);
v___y_439_ = v___x_450_;
goto v___jp_438_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; double v___x_453_; 
v___x_451_ = l_Lean_trace_profiler_threshold;
v___x_452_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_371_, v___x_451_);
v___x_453_ = lean_float_of_nat(v___x_452_);
v___y_439_ = v___x_453_;
goto v___jp_438_;
}
}
v___jp_381_:
{
lean_object* v___x_385_; 
lean_inc(v___y_383_);
v___x_385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_373_, v_data_384_, v___y_383_, v___y_382_, v___y_376_, v___y_377_);
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
v___y_382_ = v_a_393_;
v___y_383_ = v___y_392_;
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
v___y_382_ = v_a_393_;
v___y_383_ = v___y_392_;
v_data_384_ = v_data_399_;
goto v___jp_381_;
}
}
v___jp_402_:
{
lean_object* v_ref_403_; lean_object* v___x_404_; 
v_ref_403_ = lean_ctor_get(v___y_376_, 4);
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
lean_object* v___x_409_; lean_object* v_traceState_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_cache_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_437_; 
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
v_messages_416_ = lean_ctor_get(v___x_409_, 6);
v_infoState_417_ = lean_ctor_get(v___x_409_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_409_, 8);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_437_ == 0)
{
v___x_420_ = v___x_409_;
v_isShared_421_ = v_isSharedCheck_437_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_409_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_437_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint64_t v_tid_422_; lean_object* v_traces_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_436_; 
v_tid_422_ = lean_ctor_get_uint64(v_traceState_410_, sizeof(void*)*1);
v_traces_423_ = lean_ctor_get(v_traceState_410_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_traceState_410_);
if (v_isSharedCheck_436_ == 0)
{
v___x_425_ = v_traceState_410_;
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_traces_423_);
lean_dec(v_traceState_410_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_373_, v_traces_423_);
lean_dec_ref(v_traces_423_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_427_);
lean_ctor_set_uint64(v_reuseFailAlloc_435_, sizeof(void*)*1, v_tid_422_);
v___x_429_ = v_reuseFailAlloc_435_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 4, v___x_429_);
v___x_431_ = v___x_420_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_env_411_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 8, v_snapshotTasks_418_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_st_ref_put(v___y_377_, v___x_431_);
v___x_433_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_379_);
return v___x_433_;
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
v___jp_438_:
{
double v___x_440_; double v___x_441_; double v___x_442_; uint8_t v___x_443_; 
v___x_440_ = lean_unbox_float(v_snd_388_);
v___x_441_ = lean_unbox_float(v_fst_387_);
v___x_442_ = lean_float_sub(v___x_440_, v___x_441_);
v___x_443_ = lean_float_decLt(v___y_439_, v___x_442_);
v___y_408_ = v___x_443_;
goto v___jp_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_454_, lean_object* v_collapsed_455_, lean_object* v_tag_456_, lean_object* v_opts_457_, lean_object* v_clsEnabled_458_, lean_object* v_oldTraces_459_, lean_object* v_msg_460_, lean_object* v_resStartStop_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_collapsed_boxed_465_; uint8_t v_clsEnabled_boxed_466_; lean_object* v_res_467_; 
v_collapsed_boxed_465_ = lean_unbox(v_collapsed_455_);
v_clsEnabled_boxed_466_ = lean_unbox(v_clsEnabled_458_);
v_res_467_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_454_, v_collapsed_boxed_465_, v_tag_456_, v_opts_457_, v_clsEnabled_boxed_466_, v_oldTraces_459_, v_msg_460_, v_resStartStop_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v_opts_457_);
return v_res_467_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_468_; double v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1000000000u);
v___x_469_ = lean_float_of_nat(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_483_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_484_ = l_Lean_Name_append(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_489_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_490_ = l_Lean_Name_append(v___x_489_, v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_512_, lean_object* v_s_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v_a_528_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___y_547_; lean_object* v_a_548_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v_a_561_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; uint8_t v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint8_t v___y_573_; lean_object* v___y_574_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_587_; lean_object* v_a_588_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v_a_611_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v_a_624_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; uint8_t v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v_element_718_; lean_object* v_children_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_889_; 
v_element_718_ = lean_ctor_get(v_s_513_, 0);
v_children_719_ = lean_ctor_get(v_s_513_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_s_513_);
if (v_isSharedCheck_889_ == 0)
{
v___x_721_ = v_s_513_;
v_isShared_722_ = v_isSharedCheck_889_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_children_719_);
lean_inc(v_element_718_);
lean_dec(v_s_513_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_889_;
goto v_resetjp_720_;
}
v___jp_517_:
{
lean_object* v___x_529_; double v___x_530_; double v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_529_ = lean_io_get_num_heartbeats();
v___x_530_ = lean_float_of_nat(v___y_525_);
v___x_531_ = lean_float_of_nat(v___x_529_);
v___x_532_ = lean_box_float(v___x_530_);
v___x_533_ = lean_box_float(v___x_531_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_a_528_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc_ref(v___y_526_);
lean_inc(v___y_524_);
v___x_536_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_524_, v___y_527_, v___y_526_, v___y_520_, v___y_522_, v___y_521_, v___y_519_, v___x_535_, v___y_518_, v___y_523_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_a_548_);
v___y_518_ = v___y_540_;
v___y_519_ = v___y_539_;
v___y_520_ = v___y_538_;
v___y_521_ = v___y_541_;
v___y_522_ = v___y_542_;
v___y_523_ = v___y_545_;
v___y_524_ = v___y_544_;
v___y_525_ = v___y_543_;
v___y_526_ = v___y_546_;
v___y_527_ = v___y_547_;
v_a_528_ = v___x_549_;
goto v___jp_517_;
}
v___jp_550_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_a_561_);
v___y_518_ = v___y_553_;
v___y_519_ = v___y_552_;
v___y_520_ = v___y_551_;
v___y_521_ = v___y_554_;
v___y_522_ = v___y_555_;
v___y_523_ = v___y_558_;
v___y_524_ = v___y_557_;
v___y_525_ = v___y_556_;
v___y_526_ = v___y_559_;
v___y_527_ = v___y_560_;
v_a_528_ = v___x_562_;
goto v___jp_517_;
}
v___jp_563_:
{
if (lean_obj_tag(v___y_574_) == 0)
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___y_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___y_574_, 1);
v___y_538_ = v___y_566_;
v___y_539_ = v___y_565_;
v___y_540_ = v___y_564_;
v___y_541_ = v___y_567_;
v___y_542_ = v___y_568_;
v___y_543_ = v___y_571_;
v___y_544_ = v___y_570_;
v___y_545_ = v___y_569_;
v___y_546_ = v___y_572_;
v___y_547_ = v___y_573_;
v_a_548_ = v_a_575_;
goto v___jp_537_;
}
else
{
lean_object* v_a_576_; 
v_a_576_ = lean_ctor_get(v___y_574_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___y_574_, 1);
v___y_551_ = v___y_566_;
v___y_552_ = v___y_565_;
v___y_553_ = v___y_564_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_568_;
v___y_556_ = v___y_571_;
v___y_557_ = v___y_570_;
v___y_558_ = v___y_569_;
v___y_559_ = v___y_572_;
v___y_560_ = v___y_573_;
v_a_561_ = v_a_576_;
goto v___jp_550_;
}
}
v___jp_577_:
{
lean_object* v___x_589_; double v___x_590_; double v___x_591_; double v___x_592_; double v___x_593_; double v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_589_ = lean_io_mono_nanos_now();
v___x_590_ = lean_float_of_nat(v___y_582_);
v___x_591_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_592_ = lean_float_div(v___x_590_, v___x_591_);
v___x_593_ = lean_float_of_nat(v___x_589_);
v___x_594_ = lean_float_div(v___x_593_, v___x_591_);
v___x_595_ = lean_box_float(v___x_592_);
v___x_596_ = lean_box_float(v___x_594_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_588_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
v___x_599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_585_, v___y_587_, v___y_586_, v___y_580_, v___y_583_, v___y_581_, v___y_579_, v___x_598_, v___y_578_, v___y_584_);
return v___x_599_;
}
v___jp_600_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_a_611_);
v___y_578_ = v___y_603_;
v___y_579_ = v___y_602_;
v___y_580_ = v___y_601_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_605_;
v___y_583_ = v___y_606_;
v___y_584_ = v___y_608_;
v___y_585_ = v___y_607_;
v___y_586_ = v___y_609_;
v___y_587_ = v___y_610_;
v_a_588_ = v___x_612_;
goto v___jp_577_;
}
v___jp_613_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_a_624_);
v___y_578_ = v___y_616_;
v___y_579_ = v___y_615_;
v___y_580_ = v___y_614_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_618_;
v___y_583_ = v___y_619_;
v___y_584_ = v___y_621_;
v___y_585_ = v___y_620_;
v___y_586_ = v___y_622_;
v___y_587_ = v___y_623_;
v_a_588_ = v___x_625_;
goto v___jp_577_;
}
v___jp_626_:
{
if (lean_obj_tag(v___y_637_) == 0)
{
lean_object* v_a_638_; 
v_a_638_ = lean_ctor_get(v___y_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___y_637_, 1);
v___y_601_ = v___y_629_;
v___y_602_ = v___y_628_;
v___y_603_ = v___y_627_;
v___y_604_ = v___y_630_;
v___y_605_ = v___y_631_;
v___y_606_ = v___y_632_;
v___y_607_ = v___y_634_;
v___y_608_ = v___y_633_;
v___y_609_ = v___y_635_;
v___y_610_ = v___y_636_;
v_a_611_ = v_a_638_;
goto v___jp_600_;
}
else
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___y_637_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___y_637_, 1);
v___y_614_ = v___y_629_;
v___y_615_ = v___y_628_;
v___y_616_ = v___y_627_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_631_;
v___y_619_ = v___y_632_;
v___y_620_ = v___y_634_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_635_;
v___y_623_ = v___y_636_;
v_a_624_ = v_a_639_;
goto v___jp_613_;
}
}
v___jp_640_:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = l_Lean_trace_profiler_useHeartbeats;
v___x_657_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_649_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_io_mono_nanos_now();
v___x_659_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_643_, v___y_642_, v___y_652_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_dec_ref_known(v___x_659_, 1);
if (lean_obj_tag(v___y_651_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_val_660_ = lean_ctor_get(v___y_651_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v___y_651_, 1);
v___x_661_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_646_);
v___x_662_ = l_Lean_Name_mkStr2(v___y_646_, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_662_);
v___x_664_ = l_Lean_Name_append(v___x_663_, v___x_662_);
v___x_665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_648_, v___y_649_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec(v___x_662_);
lean_dec(v_val_660_);
v___x_666_ = lean_box(0);
v___y_601_ = v___y_649_;
v___y_602_ = v___y_650_;
v___y_603_ = v___y_642_;
v___y_604_ = v_a_655_;
v___y_605_ = v___x_658_;
v___y_606_ = v___y_644_;
v___y_607_ = v___y_653_;
v___y_608_ = v___y_652_;
v___y_609_ = v___y_645_;
v___y_610_ = v___y_647_;
v_a_611_ = v___x_666_;
goto v___jp_600_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box(0);
v___x_668_ = l_Lean_Elab_InfoTree_format(v_val_660_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_MessageData_ofFormat(v_a_669_);
v___x_671_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_662_, v___x_670_, v___y_642_, v___y_652_);
v___y_627_ = v___y_642_;
v___y_628_ = v___y_650_;
v___y_629_ = v___y_649_;
v___y_630_ = v_a_655_;
v___y_631_ = v___x_658_;
v___y_632_ = v___y_644_;
v___y_633_ = v___y_652_;
v___y_634_ = v___y_653_;
v___y_635_ = v___y_645_;
v___y_636_ = v___y_647_;
v___y_637_ = v___x_671_;
goto v___jp_626_;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
lean_dec(v___x_662_);
v_a_672_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_682_ == 0)
{
v___x_674_ = v___x_668_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_io_error_to_string(v_a_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 3);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Lean_MessageData_ofFormat(v___x_678_);
lean_inc(v___y_641_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___y_641_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___y_614_ = v___y_649_;
v___y_615_ = v___y_650_;
v___y_616_ = v___y_642_;
v___y_617_ = v_a_655_;
v___y_618_ = v___x_658_;
v___y_619_ = v___y_644_;
v___y_620_ = v___y_653_;
v___y_621_ = v___y_652_;
v___y_622_ = v___y_645_;
v___y_623_ = v___y_647_;
v_a_624_ = v___x_680_;
goto v___jp_613_;
}
}
}
}
}
else
{
lean_object* v___x_683_; 
lean_dec(v___y_651_);
v___x_683_ = lean_box(0);
v___y_601_ = v___y_649_;
v___y_602_ = v___y_650_;
v___y_603_ = v___y_642_;
v___y_604_ = v_a_655_;
v___y_605_ = v___x_658_;
v___y_606_ = v___y_644_;
v___y_607_ = v___y_653_;
v___y_608_ = v___y_652_;
v___y_609_ = v___y_645_;
v___y_610_ = v___y_647_;
v_a_611_ = v___x_683_;
goto v___jp_600_;
}
}
else
{
lean_dec(v___y_651_);
v___y_627_ = v___y_642_;
v___y_628_ = v___y_650_;
v___y_629_ = v___y_649_;
v___y_630_ = v_a_655_;
v___y_631_ = v___x_658_;
v___y_632_ = v___y_644_;
v___y_633_ = v___y_652_;
v___y_634_ = v___y_653_;
v___y_635_ = v___y_645_;
v___y_636_ = v___y_647_;
v___y_637_ = v___x_659_;
goto v___jp_626_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_io_get_num_heartbeats();
v___x_685_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_643_, v___y_642_, v___y_652_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_dec_ref_known(v___x_685_, 1);
if (lean_obj_tag(v___y_651_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_val_686_ = lean_ctor_get(v___y_651_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___y_651_, 1);
v___x_687_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_646_);
v___x_688_ = l_Lean_Name_mkStr2(v___y_646_, v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_688_);
v___x_690_ = l_Lean_Name_append(v___x_689_, v___x_688_);
v___x_691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_648_, v___y_649_, v___x_690_);
lean_dec(v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
lean_dec(v___x_688_);
lean_dec(v_val_686_);
v___x_692_ = lean_box(0);
v___y_538_ = v___y_649_;
v___y_539_ = v___y_650_;
v___y_540_ = v___y_642_;
v___y_541_ = v_a_655_;
v___y_542_ = v___y_644_;
v___y_543_ = v___x_684_;
v___y_544_ = v___y_653_;
v___y_545_ = v___y_652_;
v___y_546_ = v___y_645_;
v___y_547_ = v___y_647_;
v_a_548_ = v___x_692_;
goto v___jp_537_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_Elab_InfoTree_format(v_val_686_, v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Lean_MessageData_ofFormat(v_a_695_);
v___x_697_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_688_, v___x_696_, v___y_642_, v___y_652_);
v___y_564_ = v___y_642_;
v___y_565_ = v___y_650_;
v___y_566_ = v___y_649_;
v___y_567_ = v_a_655_;
v___y_568_ = v___y_644_;
v___y_569_ = v___y_652_;
v___y_570_ = v___y_653_;
v___y_571_ = v___x_684_;
v___y_572_ = v___y_645_;
v___y_573_ = v___y_647_;
v___y_574_ = v___x_697_;
goto v___jp_563_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_708_; 
lean_dec(v___x_688_);
v_a_698_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_708_ == 0)
{
v___x_700_ = v___x_694_;
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_io_error_to_string(v_a_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 3);
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_707_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = l_Lean_MessageData_ofFormat(v___x_704_);
lean_inc(v___y_641_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_641_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___y_551_ = v___y_649_;
v___y_552_ = v___y_650_;
v___y_553_ = v___y_642_;
v___y_554_ = v_a_655_;
v___y_555_ = v___y_644_;
v___y_556_ = v___x_684_;
v___y_557_ = v___y_653_;
v___y_558_ = v___y_652_;
v___y_559_ = v___y_645_;
v___y_560_ = v___y_647_;
v_a_561_ = v___x_706_;
goto v___jp_550_;
}
}
}
}
}
else
{
lean_object* v___x_709_; 
lean_dec(v___y_651_);
v___x_709_ = lean_box(0);
v___y_538_ = v___y_649_;
v___y_539_ = v___y_650_;
v___y_540_ = v___y_642_;
v___y_541_ = v_a_655_;
v___y_542_ = v___y_644_;
v___y_543_ = v___x_684_;
v___y_544_ = v___y_653_;
v___y_545_ = v___y_652_;
v___y_546_ = v___y_645_;
v___y_547_ = v___y_647_;
v_a_548_ = v___x_709_;
goto v___jp_537_;
}
}
else
{
lean_dec(v___y_651_);
v___y_564_ = v___y_642_;
v___y_565_ = v___y_650_;
v___y_566_ = v___y_649_;
v___y_567_ = v_a_655_;
v___y_568_ = v___y_644_;
v___y_569_ = v___y_652_;
v___y_570_ = v___y_653_;
v___y_571_ = v___x_684_;
v___y_572_ = v___y_645_;
v___y_573_ = v___y_647_;
v___y_574_ = v___x_685_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_643_);
v_a_710_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_654_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_654_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
v_resetjp_720_:
{
lean_object* v_desc_723_; lean_object* v_diagnostics_724_; lean_object* v_infoTree_x3f_725_; lean_object* v_desc_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___x_824_; 
v_desc_723_ = lean_ctor_get(v_element_718_, 0);
lean_inc_ref(v_desc_723_);
v_diagnostics_724_ = lean_ctor_get(v_element_718_, 1);
lean_inc_ref(v_diagnostics_724_);
v_infoTree_x3f_725_ = lean_ctor_get(v_element_718_, 2);
lean_inc(v_infoTree_x3f_725_);
lean_dec_ref(v_element_718_);
v___x_824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_824_, 0, v_desc_723_);
switch(lean_obj_tag(v_range_x3f_512_))
{
case 0:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v_desc_727_ = v___x_826_;
v___y_728_ = v_a_514_;
v___y_729_ = v_a_515_;
goto v___jp_726_;
}
case 1:
{
lean_object* v_toCold_827_; lean_object* v_range_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_886_; 
v_toCold_827_ = lean_ctor_get(v_a_514_, 0);
v_range_828_ = lean_ctor_get(v_range_x3f_512_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_range_x3f_512_);
if (v_isSharedCheck_886_ == 0)
{
v___x_830_ = v_range_x3f_512_;
v_isShared_831_ = v_isSharedCheck_886_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_range_828_);
lean_dec(v_range_x3f_512_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_886_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_fileMap_832_; lean_object* v_start_833_; lean_object* v_stop_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_885_; 
v_fileMap_832_ = lean_ctor_get(v_toCold_827_, 1);
v_start_833_ = lean_ctor_get(v_range_828_, 0);
v_stop_834_ = lean_ctor_get(v_range_828_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_range_828_);
if (v_isSharedCheck_885_ == 0)
{
v___x_836_ = v_range_828_;
v_isShared_837_ = v_isSharedCheck_885_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_stop_834_);
lean_inc(v_start_833_);
lean_dec(v_range_828_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_885_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_line_839_; lean_object* v_column_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_884_; 
lean_inc_ref(v_fileMap_832_);
v___x_838_ = l_Lean_FileMap_toPosition(v_fileMap_832_, v_start_833_);
lean_dec(v_start_833_);
v_line_839_ = lean_ctor_get(v___x_838_, 0);
v_column_840_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_884_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_column_840_);
lean_inc(v_line_839_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v_line_845_; lean_object* v_column_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_883_; 
lean_inc_ref(v_fileMap_832_);
v___x_844_ = l_Lean_FileMap_toPosition(v_fileMap_832_, v_stop_834_);
lean_dec(v_stop_834_);
v_line_845_ = lean_ctor_get(v___x_844_, 0);
v_column_846_ = lean_ctor_get(v___x_844_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_883_ == 0)
{
v___x_848_ = v___x_844_;
v_isShared_849_ = v_isSharedCheck_883_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_column_846_);
lean_inc(v_line_845_);
lean_dec(v___x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_883_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_851_ = l_Nat_reprFast(v_line_839_);
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 3);
lean_ctor_set(v___x_830_, 0, v___x_851_);
v___x_853_ = v___x_830_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_882_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 5);
lean_ctor_set(v___x_848_, 1, v___x_853_);
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_855_ = v___x_848_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_881_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 5);
lean_ctor_set(v___x_842_, 1, v___x_856_);
lean_ctor_set(v___x_842_, 0, v___x_855_);
v___x_858_ = v___x_842_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_880_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_859_ = l_Nat_reprFast(v_column_840_);
v___x_860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 5);
lean_ctor_set(v___x_836_, 1, v___x_860_);
lean_ctor_set(v___x_836_, 0, v___x_858_);
v___x_862_ = v___x_836_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_879_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Nat_reprFast(v_line_845_);
v___x_868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_850_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_856_);
v___x_871_ = l_Nat_reprFast(v_column_846_);
v___x_872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_863_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_866_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_824_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v_desc_727_ = v___x_878_;
v___y_728_ = v_a_514_;
v___y_729_ = v_a_515_;
goto v___jp_726_;
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
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_824_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v_desc_727_ = v___x_888_;
v___y_728_ = v_a_514_;
v___y_729_ = v_a_515_;
goto v___jp_726_;
}
}
v___jp_726_:
{
lean_object* v_msgLog_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_822_; 
v_msgLog_730_ = lean_ctor_get(v_diagnostics_724_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_diagnostics_724_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_diagnostics_724_, 1);
lean_dec(v_unused_823_);
v___x_732_ = v_diagnostics_724_;
v_isShared_733_ = v_isSharedCheck_822_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_msgLog_730_);
lean_dec(v_diagnostics_724_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_822_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = l_Lean_MessageLog_toList(v_msgLog_730_);
lean_dec_ref(v_msgLog_730_);
v___x_735_ = lean_box(0);
v___x_736_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_734_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_options_737_; lean_object* v_a_738_; lean_object* v_toCold_739_; lean_object* v_ref_740_; uint8_t v_hasTrace_741_; lean_object* v___x_742_; 
v_options_737_ = lean_ctor_get(v___y_728_, 1);
v_a_738_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_736_, 1);
v_toCold_739_ = lean_ctor_get(v___y_728_, 0);
v_ref_740_ = lean_ctor_get(v___y_728_, 4);
v_hasTrace_741_ = lean_ctor_get_uint8(v_options_737_, sizeof(void*)*1);
v___x_742_ = lean_array_to_list(v_children_719_);
if (v_hasTrace_741_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_a_738_);
lean_del_object(v___x_732_);
lean_dec(v_desc_727_);
lean_del_object(v___x_721_);
v___x_743_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_742_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_755_; 
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_756_);
v___x_745_ = v___x_743_;
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
else
{
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
if (lean_obj_tag(v_infoTree_x3f_725_) == 1)
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec_ref_known(v_infoTree_x3f_725_, 1);
v___x_747_ = lean_box(0);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v_infoTree_x3f_725_);
v___x_751_ = lean_box(0);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_751_);
v___x_753_ = v___x_745_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_725_);
return v___x_743_;
}
}
else
{
lean_object* v_inheritedTraceOptions_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v_inheritedTraceOptions_757_ = lean_ctor_get(v_toCold_739_, 4);
v___x_758_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_759_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_760_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_759_, v_a_738_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 5);
lean_ctor_set(v___x_732_, 1, v___x_760_);
lean_ctor_set(v___x_732_, 0, v_desc_727_);
v___x_762_ = v___x_732_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_desc_727_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_813_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___f_763_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_763_, 0, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_765_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_766_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_757_, v_options_737_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_trace_profiler;
v___x_769_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_737_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___f_763_);
v___x_770_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_742_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_811_; 
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_770_, 0);
lean_dec(v_unused_812_);
v___x_772_ = v___x_770_;
v_isShared_773_ = v_isSharedCheck_811_;
goto v_resetjp_771_;
}
else
{
lean_dec(v___x_770_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_811_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
if (lean_obj_tag(v_infoTree_x3f_725_) == 1)
{
lean_object* v_val_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_806_; 
v_val_774_ = lean_ctor_get(v_infoTree_x3f_725_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_infoTree_x3f_725_);
if (v_isSharedCheck_806_ == 0)
{
v___x_776_ = v_infoTree_x3f_725_;
v_isShared_777_ = v_isSharedCheck_806_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_val_774_);
lean_dec(v_infoTree_x3f_725_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_806_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_779_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_757_, v_options_737_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_del_object(v___x_776_);
lean_dec(v_val_774_);
lean_del_object(v___x_721_);
v___x_781_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_781_);
v___x_783_ = v___x_772_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_772_);
v___x_785_ = lean_box(0);
v___x_786_ = l_Lean_Elab_InfoTree_format(v_val_774_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_776_);
lean_del_object(v___x_721_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = l_Lean_MessageData_ofFormat(v_a_787_);
v___x_789_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_778_, v___x_788_, v___y_728_, v___y_729_);
return v___x_789_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_805_; 
v_a_790_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_805_ == 0)
{
v___x_792_ = v___x_786_;
v_isShared_793_ = v_isSharedCheck_805_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_805_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_io_error_to_string(v_a_790_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 3);
lean_ctor_set(v___x_776_, 0, v___x_794_);
v___x_796_ = v___x_776_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_804_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = l_Lean_MessageData_ofFormat(v___x_796_);
lean_inc(v_ref_740_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_797_);
lean_ctor_set(v___x_721_, 0, v_ref_740_);
v___x_799_ = v___x_721_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_ref_740_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_799_);
v___x_801_ = v___x_792_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
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
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v_infoTree_x3f_725_);
lean_del_object(v___x_721_);
v___x_807_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_807_);
v___x_809_ = v___x_772_;
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
}
}
else
{
lean_dec(v_infoTree_x3f_725_);
lean_del_object(v___x_721_);
return v___x_770_;
}
}
else
{
lean_del_object(v___x_721_);
v___y_641_ = v_ref_740_;
v___y_642_ = v___y_728_;
v___y_643_ = v___x_742_;
v___y_644_ = v___x_767_;
v___y_645_ = v___x_765_;
v___y_646_ = v___x_758_;
v___y_647_ = v_hasTrace_741_;
v___y_648_ = v_inheritedTraceOptions_757_;
v___y_649_ = v_options_737_;
v___y_650_ = v___f_763_;
v___y_651_ = v_infoTree_x3f_725_;
v___y_652_ = v___y_729_;
v___y_653_ = v___x_764_;
goto v___jp_640_;
}
}
else
{
lean_del_object(v___x_721_);
v___y_641_ = v_ref_740_;
v___y_642_ = v___y_728_;
v___y_643_ = v___x_742_;
v___y_644_ = v___x_767_;
v___y_645_ = v___x_765_;
v___y_646_ = v___x_758_;
v___y_647_ = v_hasTrace_741_;
v___y_648_ = v_inheritedTraceOptions_757_;
v___y_649_ = v_options_737_;
v___y_650_ = v___f_763_;
v___y_651_ = v_infoTree_x3f_725_;
v___y_652_ = v___y_729_;
v___y_653_ = v___x_764_;
goto v___jp_640_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_732_);
lean_dec(v_desc_727_);
lean_dec(v_infoTree_x3f_725_);
lean_del_object(v___x_721_);
lean_dec_ref(v_children_719_);
v_a_814_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_736_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_736_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
if (lean_obj_tag(v_as_890_) == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_box(0);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v_reportingRange_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_head_896_ = lean_ctor_get(v_as_890_, 0);
lean_inc(v_head_896_);
v_tail_897_ = lean_ctor_get(v_as_890_, 1);
lean_inc(v_tail_897_);
lean_dec_ref_known(v_as_890_, 2);
v_reportingRange_898_ = lean_ctor_get(v_head_896_, 1);
lean_inc(v_reportingRange_898_);
v___x_899_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_896_);
v___x_900_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_898_, v___x_899_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_dec_ref_known(v___x_900_, 1);
v_as_890_ = v_tail_897_;
goto _start;
}
else
{
lean_dec(v_tail_897_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_907_, lean_object* v_s_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_907_, v_s_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_913_, v_x_914_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_919_, v_x_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_931_, lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_931_, v_x_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_box(2);
v___x_942_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_941_, v_s_937_, v_a_938_, v_a_939_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Language_SnapshotTree_trace(v_s_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_947_;
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

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
lean_object* v___x_105_; lean_object* v_toCold_106_; lean_object* v_env_107_; lean_object* v_options_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_toCold_106_ = lean_ctor_get(v___y_102_, 0);
v_env_107_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_105_);
v_options_108_ = lean_ctor_get(v_toCold_106_, 2);
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
lean_ctor_set(v___x_112_, 1, v_msgData_101_);
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
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_175_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 2);
v___x_130_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_175_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_175_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_175_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v_traceState_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_cache_141_; lean_object* v_messages_142_; lean_object* v_infoState_143_; lean_object* v_snapshotTasks_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_174_; 
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
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_174_ == 0)
{
v___x_146_ = v___x_135_;
v_isShared_147_ = v_isSharedCheck_174_;
goto v_resetjp_145_;
}
else
{
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
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_174_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint64_t v_tid_148_; lean_object* v_traces_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_173_; 
v_tid_148_ = lean_ctor_get_uint64(v_traceState_136_, sizeof(void*)*1);
v_traces_149_ = lean_ctor_get(v_traceState_136_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_traceState_136_);
if (v_isSharedCheck_173_ == 0)
{
v___x_151_ = v_traceState_136_;
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_traces_149_);
lean_dec(v_traceState_136_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; double v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_153_ = lean_box(0);
v___x_154_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_155_ = 0;
v___x_156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_157_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_157_, 0, v_cls_124_);
lean_ctor_set(v___x_157_, 1, v___x_153_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set_float(v___x_157_, sizeof(void*)*3, v___x_154_);
lean_ctor_set_float(v___x_157_, sizeof(void*)*3 + 8, v___x_154_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*3 + 16, v___x_155_);
v___x_158_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_159_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v_a_131_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
lean_inc(v_ref_129_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_ref_129_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_PersistentArray_push___redArg(v_traces_149_, v___x_160_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_161_);
v___x_163_ = v___x_151_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_161_);
lean_ctor_set_uint64(v_reuseFailAlloc_172_, sizeof(void*)*1, v_tid_148_);
v___x_163_ = v_reuseFailAlloc_172_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v___x_163_);
v___x_165_ = v___x_146_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_env_137_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_171_, 5, v_cache_141_);
lean_ctor_set(v_reuseFailAlloc_171_, 6, v_messages_142_);
lean_ctor_set(v_reuseFailAlloc_171_, 7, v_infoState_143_);
lean_ctor_set(v_reuseFailAlloc_171_, 8, v_snapshotTasks_144_);
v___x_165_ = v_reuseFailAlloc_171_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_st_ref_put(v___y_127_, v___x_165_);
v___x_167_ = lean_box(0);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_167_);
v___x_169_ = v___x_133_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_176_, lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_176_, v_msg_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_dec(v_pre_182_);
return v_x_183_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_head_185_ = lean_ctor_get(v_x_184_, 0);
v_tail_186_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v_x_184_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_head_185_);
lean_dec(v_x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
lean_inc(v_pre_182_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 5);
lean_ctor_set(v___x_188_, 1, v_pre_182_);
lean_ctor_set(v___x_188_, 0, v_x_183_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_x_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_pre_182_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_192_, 0, v_head_185_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v_x_183_ = v___x_193_;
v_x_184_ = v_tail_186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v___x_199_; 
lean_dec(v_pre_197_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v_head_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_210_; 
v_head_200_ = lean_ctor_get(v_x_198_, 0);
v_tail_201_ = lean_ctor_get(v_x_198_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_head_200_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_205_, 0, v_head_200_);
lean_inc(v_pre_197_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 5);
lean_ctor_set(v___x_203_, 1, v___x_205_);
lean_ctor_set(v___x_203_, 0, v_pre_197_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_pre_197_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_197_, v___x_207_, v_tail_201_);
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = l_List_reverse___redArg(v_x_212_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v_head_216_; lean_object* v_tail_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_227_; 
v_head_216_ = lean_ctor_get(v_x_211_, 0);
v_tail_217_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_227_ == 0)
{
v___x_219_ = v_x_211_;
v_isShared_220_ = v_isSharedCheck_227_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_tail_217_);
lean_inc(v_head_216_);
lean_dec(v_x_211_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_227_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = 0;
v___x_222_ = l_Lean_Message_toString(v_head_216_, v___x_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v_x_212_);
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_x_212_);
v___x_224_ = v_reuseFailAlloc_226_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v_x_211_ = v_tail_217_;
v_x_212_ = v___x_224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_228_, v_x_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v_x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v_x_232_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v_x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 1);
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v_x_232_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v_x_232_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v_x_232_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 0);
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_253_, lean_object* v_opt_254_){
_start:
{
lean_object* v_name_255_; lean_object* v_defValue_256_; lean_object* v_map_257_; lean_object* v___x_258_; 
v_name_255_ = lean_ctor_get(v_opt_254_, 0);
v_defValue_256_ = lean_ctor_get(v_opt_254_, 1);
v_map_257_ = lean_ctor_get(v_opts_253_, 0);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_257_, v_name_255_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_inc(v_defValue_256_);
return v_defValue_256_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_258_, 1);
if (lean_obj_tag(v_val_259_) == 3)
{
lean_object* v_v_260_; 
v_v_260_ = lean_ctor_get(v_val_259_, 0);
lean_inc(v_v_260_);
lean_dec_ref_known(v_val_259_, 1);
return v_v_260_;
}
else
{
lean_dec(v_val_259_);
lean_inc(v_defValue_256_);
return v_defValue_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_261_, lean_object* v_opt_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_261_, v_opt_262_);
lean_dec_ref(v_opt_262_);
lean_dec_ref(v_opts_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_264_, size_t v_i_265_, lean_object* v_bs_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_lt(v_i_265_, v_sz_264_);
if (v___x_267_ == 0)
{
return v_bs_266_;
}
else
{
lean_object* v_v_268_; lean_object* v_msg_269_; lean_object* v___x_270_; lean_object* v_bs_x27_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v_v_268_ = lean_array_uget_borrowed(v_bs_266_, v_i_265_);
v_msg_269_ = lean_ctor_get(v_v_268_, 1);
lean_inc_ref(v_msg_269_);
v___x_270_ = lean_unsigned_to_nat(0u);
v_bs_x27_271_ = lean_array_uset(v_bs_266_, v_i_265_, v___x_270_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_265_, v___x_272_);
v___x_274_ = lean_array_uset(v_bs_x27_271_, v_i_265_, v_msg_269_);
v_i_265_ = v___x_273_;
v_bs_266_ = v___x_274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_276_, lean_object* v_i_277_, lean_object* v_bs_278_){
_start:
{
size_t v_sz_boxed_279_; size_t v_i_boxed_280_; lean_object* v_res_281_; 
v_sz_boxed_279_ = lean_unbox_usize(v_sz_276_);
lean_dec(v_sz_276_);
v_i_boxed_280_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_279_, v_i_boxed_280_, v_bs_278_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_282_, lean_object* v_data_283_, lean_object* v_ref_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_toCold_289_; lean_object* v_currRecDepth_290_; lean_object* v_ref_291_; uint8_t v_diag_292_; uint8_t v_suppressElabErrors_293_; lean_object* v___x_294_; lean_object* v_traceState_295_; lean_object* v_traces_296_; lean_object* v_ref_297_; lean_object* v___x_298_; lean_object* v___x_299_; size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v_msg_303_; lean_object* v___x_304_; lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_342_; 
v_toCold_289_ = lean_ctor_get(v___y_286_, 0);
v_currRecDepth_290_ = lean_ctor_get(v___y_286_, 1);
v_ref_291_ = lean_ctor_get(v___y_286_, 2);
v_diag_292_ = lean_ctor_get_uint8(v___y_286_, sizeof(void*)*3);
v_suppressElabErrors_293_ = lean_ctor_get_uint8(v___y_286_, sizeof(void*)*3 + 1);
v___x_294_ = lean_st_ref_get(v___y_287_);
v_traceState_295_ = lean_ctor_get(v___x_294_, 4);
lean_inc_ref(v_traceState_295_);
lean_dec(v___x_294_);
v_traces_296_ = lean_ctor_get(v_traceState_295_, 0);
lean_inc_ref(v_traces_296_);
lean_dec_ref(v_traceState_295_);
v_ref_297_ = l_Lean_replaceRef(v_ref_284_, v_ref_291_);
lean_inc(v_currRecDepth_290_);
lean_inc_ref(v_toCold_289_);
v___x_298_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_298_, 0, v_toCold_289_);
lean_ctor_set(v___x_298_, 1, v_currRecDepth_290_);
lean_ctor_set(v___x_298_, 2, v_ref_297_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*3, v_diag_292_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*3 + 1, v_suppressElabErrors_293_);
v___x_299_ = l_Lean_PersistentArray_toArray___redArg(v_traces_296_);
lean_dec_ref(v_traces_296_);
v_sz_300_ = lean_array_size(v___x_299_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_300_, v___x_301_, v___x_299_);
v_msg_303_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_303_, 0, v_data_283_);
lean_ctor_set(v_msg_303_, 1, v_msg_285_);
lean_ctor_set(v_msg_303_, 2, v___x_302_);
v___x_304_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_303_, v___x_298_, v___y_287_);
lean_dec_ref_known(v___x_298_, 3);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_342_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_342_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_342_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v_traceState_310_; lean_object* v_env_311_; lean_object* v_nextMacroScope_312_; lean_object* v_ngen_313_; lean_object* v_auxDeclNGen_314_; lean_object* v_cache_315_; lean_object* v_messages_316_; lean_object* v_infoState_317_; lean_object* v_snapshotTasks_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_341_; 
v___x_309_ = lean_st_ref_take(v___y_287_);
v_traceState_310_ = lean_ctor_get(v___x_309_, 4);
v_env_311_ = lean_ctor_get(v___x_309_, 0);
v_nextMacroScope_312_ = lean_ctor_get(v___x_309_, 1);
v_ngen_313_ = lean_ctor_get(v___x_309_, 2);
v_auxDeclNGen_314_ = lean_ctor_get(v___x_309_, 3);
v_cache_315_ = lean_ctor_get(v___x_309_, 5);
v_messages_316_ = lean_ctor_get(v___x_309_, 6);
v_infoState_317_ = lean_ctor_get(v___x_309_, 7);
v_snapshotTasks_318_ = lean_ctor_get(v___x_309_, 8);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_341_ == 0)
{
v___x_320_ = v___x_309_;
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_snapshotTasks_318_);
lean_inc(v_infoState_317_);
lean_inc(v_messages_316_);
lean_inc(v_cache_315_);
lean_inc(v_traceState_310_);
lean_inc(v_auxDeclNGen_314_);
lean_inc(v_ngen_313_);
lean_inc(v_nextMacroScope_312_);
lean_inc(v_env_311_);
lean_dec(v___x_309_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint64_t v_tid_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_339_; 
v_tid_322_ = lean_ctor_get_uint64(v_traceState_310_, sizeof(void*)*1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_traceState_310_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_traceState_310_, 0);
lean_dec(v_unused_340_);
v___x_324_ = v_traceState_310_;
v_isShared_325_ = v_isSharedCheck_339_;
goto v_resetjp_323_;
}
else
{
lean_dec(v_traceState_310_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_339_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_ref_284_);
lean_ctor_set(v___x_326_, 1, v_a_305_);
v___x_327_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_282_, v___x_326_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_327_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_327_);
lean_ctor_set_uint64(v_reuseFailAlloc_338_, sizeof(void*)*1, v_tid_322_);
v___x_329_ = v_reuseFailAlloc_338_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_329_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_env_311_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_nextMacroScope_312_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_ngen_313_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_auxDeclNGen_314_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v_cache_315_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_messages_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_infoState_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_snapshotTasks_318_);
v___x_331_ = v_reuseFailAlloc_337_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_st_ref_put(v___y_287_, v___x_331_);
v___x_333_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_333_);
v___x_335_ = v___x_307_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_343_, lean_object* v_data_344_, lean_object* v_ref_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_343_, v_data_344_, v_ref_345_, v_msg_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_351_){
_start:
{
if (lean_obj_tag(v_e_351_) == 0)
{
uint8_t v___x_352_; 
v___x_352_ = 2;
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_354_);
lean_dec_ref(v_e_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_360_; double v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1000u);
v___x_361_ = lean_float_of_nat(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_362_, uint8_t v_collapsed_363_, lean_object* v_tag_364_, lean_object* v_opts_365_, uint8_t v_clsEnabled_366_, lean_object* v_oldTraces_367_, lean_object* v_msg_368_, lean_object* v_resStartStop_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v_data_378_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___y_386_; lean_object* v_a_387_; uint8_t v___y_402_; double v___y_433_; 
v_fst_373_ = lean_ctor_get(v_resStartStop_369_, 0);
lean_inc(v_fst_373_);
v_snd_374_ = lean_ctor_get(v_resStartStop_369_, 1);
lean_inc(v_snd_374_);
lean_dec_ref(v_resStartStop_369_);
v_fst_381_ = lean_ctor_get(v_snd_374_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v_snd_374_, 1);
lean_inc(v_snd_382_);
lean_dec(v_snd_374_);
v___x_383_ = l_Lean_trace_profiler;
v___x_384_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_365_, v___x_383_);
if (v___x_384_ == 0)
{
v___y_402_ = v___x_384_;
goto v___jp_401_;
}
else
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = l_Lean_trace_profiler_useHeartbeats;
v___x_439_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_365_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; double v___x_442_; double v___x_443_; double v___x_444_; 
v___x_440_ = l_Lean_trace_profiler_threshold;
v___x_441_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_365_, v___x_440_);
v___x_442_ = lean_float_of_nat(v___x_441_);
v___x_443_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_444_ = lean_float_div(v___x_442_, v___x_443_);
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; double v___x_447_; 
v___x_445_ = l_Lean_trace_profiler_threshold;
v___x_446_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_365_, v___x_445_);
v___x_447_ = lean_float_of_nat(v___x_446_);
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
}
v___jp_375_:
{
lean_object* v___x_379_; 
lean_inc(v___y_377_);
v___x_379_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_367_, v_data_378_, v___y_377_, v___y_376_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_373_);
return v___x_380_;
}
else
{
lean_dec(v_fst_373_);
return v___x_379_;
}
}
v___jp_385_:
{
uint8_t v_result_388_; lean_object* v___x_389_; lean_object* v___x_390_; double v___x_391_; lean_object* v_data_392_; 
v_result_388_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_373_);
v___x_389_ = lean_box(v_result_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
v___x_391_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_364_);
lean_inc_ref(v___x_390_);
lean_inc(v_cls_362_);
v_data_392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_392_, 0, v_cls_362_);
lean_ctor_set(v_data_392_, 1, v___x_390_);
lean_ctor_set(v_data_392_, 2, v_tag_364_);
lean_ctor_set_float(v_data_392_, sizeof(void*)*3, v___x_391_);
lean_ctor_set_float(v_data_392_, sizeof(void*)*3 + 8, v___x_391_);
lean_ctor_set_uint8(v_data_392_, sizeof(void*)*3 + 16, v_collapsed_363_);
if (v___x_384_ == 0)
{
lean_dec_ref_known(v___x_390_, 1);
lean_dec(v_snd_382_);
lean_dec(v_fst_381_);
lean_dec_ref(v_tag_364_);
lean_dec(v_cls_362_);
v___y_376_ = v_a_387_;
v___y_377_ = v___y_386_;
v_data_378_ = v_data_392_;
goto v___jp_375_;
}
else
{
lean_object* v_data_393_; double v___x_394_; double v___x_395_; 
lean_dec_ref_known(v_data_392_, 3);
v_data_393_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_393_, 0, v_cls_362_);
lean_ctor_set(v_data_393_, 1, v___x_390_);
lean_ctor_set(v_data_393_, 2, v_tag_364_);
v___x_394_ = lean_unbox_float(v_fst_381_);
lean_dec(v_fst_381_);
lean_ctor_set_float(v_data_393_, sizeof(void*)*3, v___x_394_);
v___x_395_ = lean_unbox_float(v_snd_382_);
lean_dec(v_snd_382_);
lean_ctor_set_float(v_data_393_, sizeof(void*)*3 + 8, v___x_395_);
lean_ctor_set_uint8(v_data_393_, sizeof(void*)*3 + 16, v_collapsed_363_);
v___y_376_ = v_a_387_;
v___y_377_ = v___y_386_;
v_data_378_ = v_data_393_;
goto v___jp_375_;
}
}
v___jp_396_:
{
lean_object* v_ref_397_; lean_object* v___x_398_; 
v_ref_397_ = lean_ctor_get(v___y_370_, 2);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
lean_inc(v_fst_373_);
v___x_398_ = lean_apply_4(v_msg_368_, v_fst_373_, v___y_370_, v___y_371_, lean_box(0));
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___y_386_ = v_ref_397_;
v_a_387_ = v_a_399_;
goto v___jp_385_;
}
else
{
lean_object* v___x_400_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_386_ = v_ref_397_;
v_a_387_ = v___x_400_;
goto v___jp_385_;
}
}
v___jp_401_:
{
if (v_clsEnabled_366_ == 0)
{
if (v___y_402_ == 0)
{
lean_object* v___x_403_; lean_object* v_traceState_404_; lean_object* v_env_405_; lean_object* v_nextMacroScope_406_; lean_object* v_ngen_407_; lean_object* v_auxDeclNGen_408_; lean_object* v_cache_409_; lean_object* v_messages_410_; lean_object* v_infoState_411_; lean_object* v_snapshotTasks_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_snd_382_);
lean_dec(v_fst_381_);
lean_dec_ref(v_msg_368_);
lean_dec_ref(v_tag_364_);
lean_dec(v_cls_362_);
v___x_403_ = lean_st_ref_take(v___y_371_);
v_traceState_404_ = lean_ctor_get(v___x_403_, 4);
v_env_405_ = lean_ctor_get(v___x_403_, 0);
v_nextMacroScope_406_ = lean_ctor_get(v___x_403_, 1);
v_ngen_407_ = lean_ctor_get(v___x_403_, 2);
v_auxDeclNGen_408_ = lean_ctor_get(v___x_403_, 3);
v_cache_409_ = lean_ctor_get(v___x_403_, 5);
v_messages_410_ = lean_ctor_get(v___x_403_, 6);
v_infoState_411_ = lean_ctor_get(v___x_403_, 7);
v_snapshotTasks_412_ = lean_ctor_get(v___x_403_, 8);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_431_ == 0)
{
v___x_414_ = v___x_403_;
v_isShared_415_ = v_isSharedCheck_431_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snapshotTasks_412_);
lean_inc(v_infoState_411_);
lean_inc(v_messages_410_);
lean_inc(v_cache_409_);
lean_inc(v_traceState_404_);
lean_inc(v_auxDeclNGen_408_);
lean_inc(v_ngen_407_);
lean_inc(v_nextMacroScope_406_);
lean_inc(v_env_405_);
lean_dec(v___x_403_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_431_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint64_t v_tid_416_; lean_object* v_traces_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
v_tid_416_ = lean_ctor_get_uint64(v_traceState_404_, sizeof(void*)*1);
v_traces_417_ = lean_ctor_get(v_traceState_404_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_traceState_404_);
if (v_isSharedCheck_430_ == 0)
{
v___x_419_ = v_traceState_404_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_traces_417_);
lean_dec(v_traceState_404_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_367_, v_traces_417_);
lean_dec_ref(v_traces_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_421_);
lean_ctor_set_uint64(v_reuseFailAlloc_429_, sizeof(void*)*1, v_tid_416_);
v___x_423_ = v_reuseFailAlloc_429_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_423_);
v___x_425_ = v___x_414_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_env_405_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_nextMacroScope_406_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_ngen_407_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_auxDeclNGen_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_cache_409_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_messages_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v_infoState_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_snapshotTasks_412_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_put(v___y_371_, v___x_425_);
v___x_427_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_373_);
return v___x_427_;
}
}
}
}
}
else
{
goto v___jp_396_;
}
}
else
{
goto v___jp_396_;
}
}
v___jp_432_:
{
double v___x_434_; double v___x_435_; double v___x_436_; uint8_t v___x_437_; 
v___x_434_ = lean_unbox_float(v_snd_382_);
v___x_435_ = lean_unbox_float(v_fst_381_);
v___x_436_ = lean_float_sub(v___x_434_, v___x_435_);
v___x_437_ = lean_float_decLt(v___y_433_, v___x_436_);
v___y_402_ = v___x_437_;
goto v___jp_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_448_, lean_object* v_collapsed_449_, lean_object* v_tag_450_, lean_object* v_opts_451_, lean_object* v_clsEnabled_452_, lean_object* v_oldTraces_453_, lean_object* v_msg_454_, lean_object* v_resStartStop_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_collapsed_boxed_459_; uint8_t v_clsEnabled_boxed_460_; lean_object* v_res_461_; 
v_collapsed_boxed_459_ = lean_unbox(v_collapsed_449_);
v_clsEnabled_boxed_460_ = lean_unbox(v_clsEnabled_452_);
v_res_461_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_448_, v_collapsed_boxed_459_, v_tag_450_, v_opts_451_, v_clsEnabled_boxed_460_, v_oldTraces_453_, v_msg_454_, v_resStartStop_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_opts_451_);
return v_res_461_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_462_; double v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(1000000000u);
v___x_463_ = lean_float_of_nat(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_477_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_478_ = l_Lean_Name_append(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_483_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_484_ = l_Lean_Name_append(v___x_483_, v___x_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_506_, lean_object* v_s_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v_a_522_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_a_542_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v_a_555_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; uint8_t v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v_a_582_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v_a_605_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v_a_618_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; uint8_t v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v_element_712_; lean_object* v_children_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_883_; 
v_element_712_ = lean_ctor_get(v_s_507_, 0);
v_children_713_ = lean_ctor_get(v_s_507_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_s_507_);
if (v_isSharedCheck_883_ == 0)
{
v___x_715_ = v_s_507_;
v_isShared_716_ = v_isSharedCheck_883_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_children_713_);
lean_inc(v_element_712_);
lean_dec(v_s_507_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_883_;
goto v_resetjp_714_;
}
v___jp_511_:
{
lean_object* v___x_523_; double v___x_524_; double v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_523_ = lean_io_get_num_heartbeats();
v___x_524_ = lean_float_of_nat(v___y_512_);
v___x_525_ = lean_float_of_nat(v___x_523_);
v___x_526_ = lean_box_float(v___x_524_);
v___x_527_ = lean_box_float(v___x_525_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_a_522_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_517_);
v___x_530_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_517_, v___y_515_, v___y_519_, v___y_521_, v___y_516_, v___y_520_, v___y_518_, v___x_529_, v___y_514_, v___y_513_);
return v___x_530_;
}
v___jp_531_:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_a_542_);
v___y_512_ = v___y_532_;
v___y_513_ = v___y_534_;
v___y_514_ = v___y_533_;
v___y_515_ = v___y_535_;
v___y_516_ = v___y_537_;
v___y_517_ = v___y_536_;
v___y_518_ = v___y_538_;
v___y_519_ = v___y_539_;
v___y_520_ = v___y_541_;
v___y_521_ = v___y_540_;
v_a_522_ = v___x_543_;
goto v___jp_511_;
}
v___jp_544_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_a_555_);
v___y_512_ = v___y_545_;
v___y_513_ = v___y_547_;
v___y_514_ = v___y_546_;
v___y_515_ = v___y_548_;
v___y_516_ = v___y_550_;
v___y_517_ = v___y_549_;
v___y_518_ = v___y_551_;
v___y_519_ = v___y_552_;
v___y_520_ = v___y_554_;
v___y_521_ = v___y_553_;
v_a_522_ = v___x_556_;
goto v___jp_511_;
}
v___jp_557_:
{
if (lean_obj_tag(v___y_568_) == 0)
{
lean_object* v_a_569_; 
v_a_569_ = lean_ctor_get(v___y_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___y_568_, 1);
v___y_532_ = v___y_558_;
v___y_533_ = v___y_560_;
v___y_534_ = v___y_559_;
v___y_535_ = v___y_561_;
v___y_536_ = v___y_563_;
v___y_537_ = v___y_562_;
v___y_538_ = v___y_564_;
v___y_539_ = v___y_565_;
v___y_540_ = v___y_567_;
v___y_541_ = v___y_566_;
v_a_542_ = v_a_569_;
goto v___jp_531_;
}
else
{
lean_object* v_a_570_; 
v_a_570_ = lean_ctor_get(v___y_568_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___y_568_, 1);
v___y_545_ = v___y_558_;
v___y_546_ = v___y_560_;
v___y_547_ = v___y_559_;
v___y_548_ = v___y_561_;
v___y_549_ = v___y_563_;
v___y_550_ = v___y_562_;
v___y_551_ = v___y_564_;
v___y_552_ = v___y_565_;
v___y_553_ = v___y_567_;
v___y_554_ = v___y_566_;
v_a_555_ = v_a_570_;
goto v___jp_544_;
}
}
v___jp_571_:
{
lean_object* v___x_583_; double v___x_584_; double v___x_585_; double v___x_586_; double v___x_587_; double v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_583_ = lean_io_mono_nanos_now();
v___x_584_ = lean_float_of_nat(v___y_572_);
v___x_585_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_586_ = lean_float_div(v___x_584_, v___x_585_);
v___x_587_ = lean_float_of_nat(v___x_583_);
v___x_588_ = lean_float_div(v___x_587_, v___x_585_);
v___x_589_ = lean_box_float(v___x_586_);
v___x_590_ = lean_box_float(v___x_588_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_a_582_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_577_);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_577_, v___y_575_, v___y_579_, v___y_581_, v___y_576_, v___y_580_, v___y_578_, v___x_592_, v___y_574_, v___y_573_);
return v___x_593_;
}
v___jp_594_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_a_605_);
v___y_572_ = v___y_595_;
v___y_573_ = v___y_597_;
v___y_574_ = v___y_596_;
v___y_575_ = v___y_598_;
v___y_576_ = v___y_600_;
v___y_577_ = v___y_599_;
v___y_578_ = v___y_601_;
v___y_579_ = v___y_602_;
v___y_580_ = v___y_604_;
v___y_581_ = v___y_603_;
v_a_582_ = v___x_606_;
goto v___jp_571_;
}
v___jp_607_:
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_a_618_);
v___y_572_ = v___y_608_;
v___y_573_ = v___y_610_;
v___y_574_ = v___y_609_;
v___y_575_ = v___y_611_;
v___y_576_ = v___y_613_;
v___y_577_ = v___y_612_;
v___y_578_ = v___y_614_;
v___y_579_ = v___y_615_;
v___y_580_ = v___y_617_;
v___y_581_ = v___y_616_;
v_a_582_ = v___x_619_;
goto v___jp_571_;
}
v___jp_620_:
{
if (lean_obj_tag(v___y_631_) == 0)
{
lean_object* v_a_632_; 
v_a_632_ = lean_ctor_get(v___y_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___y_631_, 1);
v___y_595_ = v___y_621_;
v___y_596_ = v___y_623_;
v___y_597_ = v___y_622_;
v___y_598_ = v___y_624_;
v___y_599_ = v___y_626_;
v___y_600_ = v___y_625_;
v___y_601_ = v___y_627_;
v___y_602_ = v___y_628_;
v___y_603_ = v___y_630_;
v___y_604_ = v___y_629_;
v_a_605_ = v_a_632_;
goto v___jp_594_;
}
else
{
lean_object* v_a_633_; 
v_a_633_ = lean_ctor_get(v___y_631_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___y_631_, 1);
v___y_608_ = v___y_621_;
v___y_609_ = v___y_623_;
v___y_610_ = v___y_622_;
v___y_611_ = v___y_624_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_625_;
v___y_614_ = v___y_627_;
v___y_615_ = v___y_628_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_629_;
v_a_618_ = v_a_633_;
goto v___jp_607_;
}
}
v___jp_634_:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_644_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l_Lean_trace_profiler_useHeartbeats;
v___x_651_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_640_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_io_mono_nanos_now();
v___x_653_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_647_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref_known(v___x_653_, 1);
if (lean_obj_tag(v___y_642_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_val_654_ = lean_ctor_get(v___y_642_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___y_642_, 1);
v___x_655_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_641_);
v___x_656_ = l_Lean_Name_mkStr2(v___y_641_, v___x_655_);
v___x_657_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_656_);
v___x_658_ = l_Lean_Name_append(v___x_657_, v___x_656_);
v___x_659_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_635_, v___y_640_, v___x_658_);
lean_dec(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v___x_656_);
lean_dec(v_val_654_);
v___x_660_ = lean_box(0);
v___y_595_ = v___x_652_;
v___y_596_ = v___y_643_;
v___y_597_ = v___y_644_;
v___y_598_ = v___y_645_;
v___y_599_ = v___y_637_;
v___y_600_ = v___y_646_;
v___y_601_ = v___y_638_;
v___y_602_ = v___y_639_;
v___y_603_ = v___y_640_;
v___y_604_ = v_a_649_;
v_a_605_ = v___x_660_;
goto v___jp_594_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_Elab_InfoTree_format(v_val_654_, v___x_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = l_Lean_MessageData_ofFormat(v_a_663_);
v___x_665_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_656_, v___x_664_, v___y_643_, v___y_644_);
v___y_621_ = v___x_652_;
v___y_622_ = v___y_644_;
v___y_623_ = v___y_643_;
v___y_624_ = v___y_645_;
v___y_625_ = v___y_646_;
v___y_626_ = v___y_637_;
v___y_627_ = v___y_638_;
v___y_628_ = v___y_639_;
v___y_629_ = v_a_649_;
v___y_630_ = v___y_640_;
v___y_631_ = v___x_665_;
goto v___jp_620_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___x_656_);
v_a_666_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v___x_662_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_io_error_to_string(v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 3);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_675_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = l_Lean_MessageData_ofFormat(v___x_672_);
lean_inc(v___y_636_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_636_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___y_608_ = v___x_652_;
v___y_609_ = v___y_643_;
v___y_610_ = v___y_644_;
v___y_611_ = v___y_645_;
v___y_612_ = v___y_637_;
v___y_613_ = v___y_646_;
v___y_614_ = v___y_638_;
v___y_615_ = v___y_639_;
v___y_616_ = v___y_640_;
v___y_617_ = v_a_649_;
v_a_618_ = v___x_674_;
goto v___jp_607_;
}
}
}
}
}
else
{
lean_object* v___x_677_; 
lean_dec(v___y_642_);
v___x_677_ = lean_box(0);
v___y_595_ = v___x_652_;
v___y_596_ = v___y_643_;
v___y_597_ = v___y_644_;
v___y_598_ = v___y_645_;
v___y_599_ = v___y_637_;
v___y_600_ = v___y_646_;
v___y_601_ = v___y_638_;
v___y_602_ = v___y_639_;
v___y_603_ = v___y_640_;
v___y_604_ = v_a_649_;
v_a_605_ = v___x_677_;
goto v___jp_594_;
}
}
else
{
lean_dec(v___y_642_);
v___y_621_ = v___x_652_;
v___y_622_ = v___y_644_;
v___y_623_ = v___y_643_;
v___y_624_ = v___y_645_;
v___y_625_ = v___y_646_;
v___y_626_ = v___y_637_;
v___y_627_ = v___y_638_;
v___y_628_ = v___y_639_;
v___y_629_ = v_a_649_;
v___y_630_ = v___y_640_;
v___y_631_ = v___x_653_;
goto v___jp_620_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_io_get_num_heartbeats();
v___x_679_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_647_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec_ref_known(v___x_679_, 1);
if (lean_obj_tag(v___y_642_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_val_680_ = lean_ctor_get(v___y_642_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v___y_642_, 1);
v___x_681_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_641_);
v___x_682_ = l_Lean_Name_mkStr2(v___y_641_, v___x_681_);
v___x_683_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_682_);
v___x_684_ = l_Lean_Name_append(v___x_683_, v___x_682_);
v___x_685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_635_, v___y_640_, v___x_684_);
lean_dec(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v___x_682_);
lean_dec(v_val_680_);
v___x_686_ = lean_box(0);
v___y_532_ = v___x_678_;
v___y_533_ = v___y_643_;
v___y_534_ = v___y_644_;
v___y_535_ = v___y_645_;
v___y_536_ = v___y_637_;
v___y_537_ = v___y_646_;
v___y_538_ = v___y_638_;
v___y_539_ = v___y_639_;
v___y_540_ = v___y_640_;
v___y_541_ = v_a_649_;
v_a_542_ = v___x_686_;
goto v___jp_531_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_Elab_InfoTree_format(v_val_680_, v___x_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Lean_MessageData_ofFormat(v_a_689_);
v___x_691_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_682_, v___x_690_, v___y_643_, v___y_644_);
v___y_558_ = v___x_678_;
v___y_559_ = v___y_644_;
v___y_560_ = v___y_643_;
v___y_561_ = v___y_645_;
v___y_562_ = v___y_646_;
v___y_563_ = v___y_637_;
v___y_564_ = v___y_638_;
v___y_565_ = v___y_639_;
v___y_566_ = v_a_649_;
v___y_567_ = v___y_640_;
v___y_568_ = v___x_691_;
goto v___jp_557_;
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
lean_dec(v___x_682_);
v_a_692_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v___x_688_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_688_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_io_error_to_string(v_a_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 3);
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = l_Lean_MessageData_ofFormat(v___x_698_);
lean_inc(v___y_636_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___y_636_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___y_545_ = v___x_678_;
v___y_546_ = v___y_643_;
v___y_547_ = v___y_644_;
v___y_548_ = v___y_645_;
v___y_549_ = v___y_637_;
v___y_550_ = v___y_646_;
v___y_551_ = v___y_638_;
v___y_552_ = v___y_639_;
v___y_553_ = v___y_640_;
v___y_554_ = v_a_649_;
v_a_555_ = v___x_700_;
goto v___jp_544_;
}
}
}
}
}
else
{
lean_object* v___x_703_; 
lean_dec(v___y_642_);
v___x_703_ = lean_box(0);
v___y_532_ = v___x_678_;
v___y_533_ = v___y_643_;
v___y_534_ = v___y_644_;
v___y_535_ = v___y_645_;
v___y_536_ = v___y_637_;
v___y_537_ = v___y_646_;
v___y_538_ = v___y_638_;
v___y_539_ = v___y_639_;
v___y_540_ = v___y_640_;
v___y_541_ = v_a_649_;
v_a_542_ = v___x_703_;
goto v___jp_531_;
}
}
else
{
lean_dec(v___y_642_);
v___y_558_ = v___x_678_;
v___y_559_ = v___y_644_;
v___y_560_ = v___y_643_;
v___y_561_ = v___y_645_;
v___y_562_ = v___y_646_;
v___y_563_ = v___y_637_;
v___y_564_ = v___y_638_;
v___y_565_ = v___y_639_;
v___y_566_ = v_a_649_;
v___y_567_ = v___y_640_;
v___y_568_ = v___x_679_;
goto v___jp_557_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v___y_647_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_638_);
v_a_704_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_648_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_648_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
v_resetjp_714_:
{
lean_object* v_desc_717_; lean_object* v_diagnostics_718_; lean_object* v_infoTree_x3f_719_; lean_object* v_desc_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___x_818_; 
v_desc_717_ = lean_ctor_get(v_element_712_, 0);
lean_inc_ref(v_desc_717_);
v_diagnostics_718_ = lean_ctor_get(v_element_712_, 1);
lean_inc_ref(v_diagnostics_718_);
v_infoTree_x3f_719_ = lean_ctor_get(v_element_712_, 2);
lean_inc(v_infoTree_x3f_719_);
lean_dec_ref(v_element_712_);
v___x_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_818_, 0, v_desc_717_);
switch(lean_obj_tag(v_range_x3f_506_))
{
case 0:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v_desc_721_ = v___x_820_;
v___y_722_ = v_a_508_;
v___y_723_ = v_a_509_;
goto v___jp_720_;
}
case 1:
{
lean_object* v_toCold_821_; lean_object* v_range_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_880_; 
v_toCold_821_ = lean_ctor_get(v_a_508_, 0);
v_range_822_ = lean_ctor_get(v_range_x3f_506_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_range_x3f_506_);
if (v_isSharedCheck_880_ == 0)
{
v___x_824_ = v_range_x3f_506_;
v_isShared_825_ = v_isSharedCheck_880_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_range_822_);
lean_dec(v_range_x3f_506_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_880_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fileMap_826_; lean_object* v_start_827_; lean_object* v_stop_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_879_; 
v_fileMap_826_ = lean_ctor_get(v_toCold_821_, 1);
v_start_827_ = lean_ctor_get(v_range_822_, 0);
v_stop_828_ = lean_ctor_get(v_range_822_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_range_822_);
if (v_isSharedCheck_879_ == 0)
{
v___x_830_ = v_range_822_;
v_isShared_831_ = v_isSharedCheck_879_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_stop_828_);
lean_inc(v_start_827_);
lean_dec(v_range_822_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_879_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v_line_833_; lean_object* v_column_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_878_; 
lean_inc_ref(v_fileMap_826_);
v___x_832_ = l_Lean_FileMap_toPosition(v_fileMap_826_, v_start_827_);
lean_dec(v_start_827_);
v_line_833_ = lean_ctor_get(v___x_832_, 0);
v_column_834_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_878_ == 0)
{
v___x_836_ = v___x_832_;
v_isShared_837_ = v_isSharedCheck_878_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_column_834_);
lean_inc(v_line_833_);
lean_dec(v___x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_878_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_line_839_; lean_object* v_column_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_877_; 
lean_inc_ref(v_fileMap_826_);
v___x_838_ = l_Lean_FileMap_toPosition(v_fileMap_826_, v_stop_828_);
lean_dec(v_stop_828_);
v_line_839_ = lean_ctor_get(v___x_838_, 0);
v_column_840_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_877_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_877_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_column_840_);
lean_inc(v_line_839_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_877_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_845_ = l_Nat_reprFast(v_line_833_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 3);
lean_ctor_set(v___x_824_, 0, v___x_845_);
v___x_847_ = v___x_824_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_876_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 5);
lean_ctor_set(v___x_842_, 1, v___x_847_);
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_849_ = v___x_842_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_875_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 5);
lean_ctor_set(v___x_836_, 1, v___x_850_);
lean_ctor_set(v___x_836_, 0, v___x_849_);
v___x_852_ = v___x_836_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_874_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = l_Nat_reprFast(v_column_834_);
v___x_854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 5);
lean_ctor_set(v___x_830_, 1, v___x_854_);
lean_ctor_set(v___x_830_, 0, v___x_852_);
v___x_856_ = v___x_830_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_873_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Nat_reprFast(v_line_839_);
v___x_862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_844_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_850_);
v___x_865_ = l_Nat_reprFast(v_column_840_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_864_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_857_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_860_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_818_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v_desc_721_ = v___x_872_;
v___y_722_ = v_a_508_;
v___y_723_ = v_a_509_;
goto v___jp_720_;
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
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_818_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v_desc_721_ = v___x_882_;
v___y_722_ = v_a_508_;
v___y_723_ = v_a_509_;
goto v___jp_720_;
}
}
v___jp_720_:
{
lean_object* v_msgLog_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_816_; 
v_msgLog_724_ = lean_ctor_get(v_diagnostics_718_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_diagnostics_718_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_diagnostics_718_, 1);
lean_dec(v_unused_817_);
v___x_726_ = v_diagnostics_718_;
v_isShared_727_ = v_isSharedCheck_816_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_msgLog_724_);
lean_dec(v_diagnostics_718_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_816_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_MessageLog_toList(v_msgLog_724_);
lean_dec_ref(v_msgLog_724_);
v___x_729_ = lean_box(0);
v___x_730_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_728_, v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_toCold_731_; lean_object* v_options_732_; lean_object* v_a_733_; lean_object* v_ref_734_; lean_object* v_inheritedTraceOptions_735_; uint8_t v_hasTrace_736_; lean_object* v___x_737_; 
v_toCold_731_ = lean_ctor_get(v___y_722_, 0);
v_options_732_ = lean_ctor_get(v_toCold_731_, 2);
v_a_733_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_730_, 1);
v_ref_734_ = lean_ctor_get(v___y_722_, 2);
v_inheritedTraceOptions_735_ = lean_ctor_get(v_toCold_731_, 11);
v_hasTrace_736_ = lean_ctor_get_uint8(v_options_732_, sizeof(void*)*1);
v___x_737_ = lean_array_to_list(v_children_713_);
if (v_hasTrace_736_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_a_733_);
lean_del_object(v___x_726_);
lean_dec(v_desc_721_);
lean_del_object(v___x_715_);
v___x_738_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_737_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_750_; 
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_738_, 0);
lean_dec(v_unused_751_);
v___x_740_ = v___x_738_;
v_isShared_741_ = v_isSharedCheck_750_;
goto v_resetjp_739_;
}
else
{
lean_dec(v___x_738_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_750_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_infoTree_x3f_719_) == 1)
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec_ref_known(v_infoTree_x3f_719_, 1);
v___x_742_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec(v_infoTree_x3f_719_);
v___x_746_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_746_);
v___x_748_ = v___x_740_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_719_);
return v___x_738_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_752_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_753_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_754_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_753_, v_a_733_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 5);
lean_ctor_set(v___x_726_, 1, v___x_754_);
lean_ctor_set(v___x_726_, 0, v_desc_721_);
v___x_756_ = v___x_726_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_desc_721_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_807_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___f_757_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_757_, 0, v___x_756_);
v___x_758_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_759_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_760_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_735_, v_options_732_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = l_Lean_trace_profiler;
v___x_763_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_732_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v___f_757_);
v___x_764_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_737_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_805_; 
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_806_);
v___x_766_ = v___x_764_;
v_isShared_767_ = v_isSharedCheck_805_;
goto v_resetjp_765_;
}
else
{
lean_dec(v___x_764_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_805_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
if (lean_obj_tag(v_infoTree_x3f_719_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_800_; 
v_val_768_ = lean_ctor_get(v_infoTree_x3f_719_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v_infoTree_x3f_719_);
if (v_isSharedCheck_800_ == 0)
{
v___x_770_ = v_infoTree_x3f_719_;
v_isShared_771_ = v_isSharedCheck_800_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_infoTree_x3f_719_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_800_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_773_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_735_, v_options_732_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
lean_del_object(v___x_715_);
v___x_775_ = lean_box(0);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_775_);
v___x_777_ = v___x_766_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_766_);
v___x_779_ = lean_box(0);
v___x_780_ = l_Lean_Elab_InfoTree_format(v_val_768_, v___x_779_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_del_object(v___x_770_);
lean_del_object(v___x_715_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = l_Lean_MessageData_ofFormat(v_a_781_);
v___x_783_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_772_, v___x_782_, v___y_722_, v___y_723_);
return v___x_783_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_799_; 
v_a_784_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_799_ == 0)
{
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_io_error_to_string(v_a_784_);
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 3);
lean_ctor_set(v___x_770_, 0, v___x_788_);
v___x_790_ = v___x_770_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_798_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = l_Lean_MessageData_ofFormat(v___x_790_);
lean_inc(v_ref_734_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_791_);
lean_ctor_set(v___x_715_, 0, v_ref_734_);
v___x_793_ = v___x_715_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_ref_734_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_793_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
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
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec(v_infoTree_x3f_719_);
lean_del_object(v___x_715_);
v___x_801_ = lean_box(0);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_801_);
v___x_803_ = v___x_766_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_719_);
lean_del_object(v___x_715_);
return v___x_764_;
}
}
else
{
lean_del_object(v___x_715_);
v___y_635_ = v_inheritedTraceOptions_735_;
v___y_636_ = v_ref_734_;
v___y_637_ = v___x_758_;
v___y_638_ = v___f_757_;
v___y_639_ = v___x_759_;
v___y_640_ = v_options_732_;
v___y_641_ = v___x_752_;
v___y_642_ = v_infoTree_x3f_719_;
v___y_643_ = v___y_722_;
v___y_644_ = v___y_723_;
v___y_645_ = v_hasTrace_736_;
v___y_646_ = v___x_761_;
v___y_647_ = v___x_737_;
goto v___jp_634_;
}
}
else
{
lean_del_object(v___x_715_);
v___y_635_ = v_inheritedTraceOptions_735_;
v___y_636_ = v_ref_734_;
v___y_637_ = v___x_758_;
v___y_638_ = v___f_757_;
v___y_639_ = v___x_759_;
v___y_640_ = v_options_732_;
v___y_641_ = v___x_752_;
v___y_642_ = v_infoTree_x3f_719_;
v___y_643_ = v___y_722_;
v___y_644_ = v___y_723_;
v___y_645_ = v_hasTrace_736_;
v___y_646_ = v___x_761_;
v___y_647_ = v___x_737_;
goto v___jp_634_;
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_del_object(v___x_726_);
lean_dec(v_desc_721_);
lean_dec(v_infoTree_x3f_719_);
lean_del_object(v___x_715_);
lean_dec_ref(v_children_713_);
v_a_808_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_730_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_730_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_as_884_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_head_890_; lean_object* v_tail_891_; lean_object* v_reportingRange_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_head_890_ = lean_ctor_get(v_as_884_, 0);
lean_inc(v_head_890_);
v_tail_891_ = lean_ctor_get(v_as_884_, 1);
lean_inc(v_tail_891_);
lean_dec_ref_known(v_as_884_, 2);
v_reportingRange_892_ = lean_ctor_get(v_head_890_, 1);
lean_inc(v_reportingRange_892_);
v___x_893_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_890_);
v___x_894_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_892_, v___x_893_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_dec_ref_known(v___x_894_, 1);
v_as_884_ = v_tail_891_;
goto _start;
}
else
{
lean_dec(v_tail_891_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_901_, lean_object* v_s_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_901_, v_s_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_907_, v_x_908_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_913_, v_x_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_925_, v_x_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_box(2);
v___x_936_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_935_, v_s_931_, v_a_932_, v_a_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Language_SnapshotTree_trace(v_s_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_941_;
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

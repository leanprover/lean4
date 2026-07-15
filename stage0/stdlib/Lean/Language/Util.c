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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object*);
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
lean_object* v_fileName_288_; lean_object* v_fileMap_289_; lean_object* v_options_290_; lean_object* v_currRecDepth_291_; lean_object* v_maxRecDepth_292_; lean_object* v_ref_293_; lean_object* v_currNamespace_294_; lean_object* v_openDecls_295_; lean_object* v_initHeartbeats_296_; lean_object* v_maxHeartbeats_297_; lean_object* v_quotContext_298_; lean_object* v_currMacroScope_299_; uint8_t v_diag_300_; lean_object* v_cancelTk_x3f_301_; uint8_t v_suppressElabErrors_302_; lean_object* v_inheritedTraceOptions_303_; lean_object* v___x_304_; lean_object* v_traceState_305_; lean_object* v_traces_306_; lean_object* v_ref_307_; lean_object* v___x_308_; lean_object* v___x_309_; size_t v_sz_310_; size_t v___x_311_; lean_object* v___x_312_; lean_object* v_msg_313_; lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_352_; 
v_fileName_288_ = lean_ctor_get(v___y_285_, 0);
v_fileMap_289_ = lean_ctor_get(v___y_285_, 1);
v_options_290_ = lean_ctor_get(v___y_285_, 2);
v_currRecDepth_291_ = lean_ctor_get(v___y_285_, 3);
v_maxRecDepth_292_ = lean_ctor_get(v___y_285_, 4);
v_ref_293_ = lean_ctor_get(v___y_285_, 5);
v_currNamespace_294_ = lean_ctor_get(v___y_285_, 6);
v_openDecls_295_ = lean_ctor_get(v___y_285_, 7);
v_initHeartbeats_296_ = lean_ctor_get(v___y_285_, 8);
v_maxHeartbeats_297_ = lean_ctor_get(v___y_285_, 9);
v_quotContext_298_ = lean_ctor_get(v___y_285_, 10);
v_currMacroScope_299_ = lean_ctor_get(v___y_285_, 11);
v_diag_300_ = lean_ctor_get_uint8(v___y_285_, sizeof(void*)*14);
v_cancelTk_x3f_301_ = lean_ctor_get(v___y_285_, 12);
v_suppressElabErrors_302_ = lean_ctor_get_uint8(v___y_285_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_303_ = lean_ctor_get(v___y_285_, 13);
v___x_304_ = lean_st_ref_get(v___y_286_);
v_traceState_305_ = lean_ctor_get(v___x_304_, 4);
lean_inc_ref(v_traceState_305_);
lean_dec(v___x_304_);
v_traces_306_ = lean_ctor_get(v_traceState_305_, 0);
lean_inc_ref(v_traces_306_);
lean_dec_ref(v_traceState_305_);
v_ref_307_ = l_Lean_replaceRef(v_ref_283_, v_ref_293_);
lean_inc_ref(v_inheritedTraceOptions_303_);
lean_inc(v_cancelTk_x3f_301_);
lean_inc(v_currMacroScope_299_);
lean_inc(v_quotContext_298_);
lean_inc(v_maxHeartbeats_297_);
lean_inc(v_initHeartbeats_296_);
lean_inc(v_openDecls_295_);
lean_inc(v_currNamespace_294_);
lean_inc(v_maxRecDepth_292_);
lean_inc(v_currRecDepth_291_);
lean_inc_ref(v_options_290_);
lean_inc_ref(v_fileMap_289_);
lean_inc_ref(v_fileName_288_);
v___x_308_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_308_, 0, v_fileName_288_);
lean_ctor_set(v___x_308_, 1, v_fileMap_289_);
lean_ctor_set(v___x_308_, 2, v_options_290_);
lean_ctor_set(v___x_308_, 3, v_currRecDepth_291_);
lean_ctor_set(v___x_308_, 4, v_maxRecDepth_292_);
lean_ctor_set(v___x_308_, 5, v_ref_307_);
lean_ctor_set(v___x_308_, 6, v_currNamespace_294_);
lean_ctor_set(v___x_308_, 7, v_openDecls_295_);
lean_ctor_set(v___x_308_, 8, v_initHeartbeats_296_);
lean_ctor_set(v___x_308_, 9, v_maxHeartbeats_297_);
lean_ctor_set(v___x_308_, 10, v_quotContext_298_);
lean_ctor_set(v___x_308_, 11, v_currMacroScope_299_);
lean_ctor_set(v___x_308_, 12, v_cancelTk_x3f_301_);
lean_ctor_set(v___x_308_, 13, v_inheritedTraceOptions_303_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*14, v_diag_300_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*14 + 1, v_suppressElabErrors_302_);
v___x_309_ = l_Lean_PersistentArray_toArray___redArg(v_traces_306_);
lean_dec_ref(v_traces_306_);
v_sz_310_ = lean_array_size(v___x_309_);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_310_, v___x_311_, v___x_309_);
v_msg_313_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_313_, 0, v_data_282_);
lean_ctor_set(v_msg_313_, 1, v_msg_284_);
lean_ctor_set(v_msg_313_, 2, v___x_312_);
v___x_314_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_313_, v___x_308_, v___y_286_);
lean_dec_ref_known(v___x_308_, 14);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_352_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_352_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_352_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v_traceState_320_; lean_object* v_env_321_; lean_object* v_nextMacroScope_322_; lean_object* v_ngen_323_; lean_object* v_auxDeclNGen_324_; lean_object* v_cache_325_; lean_object* v_messages_326_; lean_object* v_infoState_327_; lean_object* v_snapshotTasks_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_351_; 
v___x_319_ = lean_st_ref_take(v___y_286_);
v_traceState_320_ = lean_ctor_get(v___x_319_, 4);
v_env_321_ = lean_ctor_get(v___x_319_, 0);
v_nextMacroScope_322_ = lean_ctor_get(v___x_319_, 1);
v_ngen_323_ = lean_ctor_get(v___x_319_, 2);
v_auxDeclNGen_324_ = lean_ctor_get(v___x_319_, 3);
v_cache_325_ = lean_ctor_get(v___x_319_, 5);
v_messages_326_ = lean_ctor_get(v___x_319_, 6);
v_infoState_327_ = lean_ctor_get(v___x_319_, 7);
v_snapshotTasks_328_ = lean_ctor_get(v___x_319_, 8);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_351_ == 0)
{
v___x_330_ = v___x_319_;
v_isShared_331_ = v_isSharedCheck_351_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_snapshotTasks_328_);
lean_inc(v_infoState_327_);
lean_inc(v_messages_326_);
lean_inc(v_cache_325_);
lean_inc(v_traceState_320_);
lean_inc(v_auxDeclNGen_324_);
lean_inc(v_ngen_323_);
lean_inc(v_nextMacroScope_322_);
lean_inc(v_env_321_);
lean_dec(v___x_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_351_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint64_t v_tid_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_349_; 
v_tid_332_ = lean_ctor_get_uint64(v_traceState_320_, sizeof(void*)*1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_traceState_320_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_traceState_320_, 0);
lean_dec(v_unused_350_);
v___x_334_ = v_traceState_320_;
v_isShared_335_ = v_isSharedCheck_349_;
goto v_resetjp_333_;
}
else
{
lean_dec(v_traceState_320_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_349_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_ref_283_);
lean_ctor_set(v___x_336_, 1, v_a_315_);
v___x_337_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_281_, v___x_336_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_337_);
lean_ctor_set_uint64(v_reuseFailAlloc_348_, sizeof(void*)*1, v_tid_332_);
v___x_339_ = v_reuseFailAlloc_348_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v___x_339_);
v___x_341_ = v___x_330_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_env_321_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_nextMacroScope_322_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_ngen_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_auxDeclNGen_324_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 5, v_cache_325_);
lean_ctor_set(v_reuseFailAlloc_347_, 6, v_messages_326_);
lean_ctor_set(v_reuseFailAlloc_347_, 7, v_infoState_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 8, v_snapshotTasks_328_);
v___x_341_ = v_reuseFailAlloc_347_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = lean_st_ref_set(v___y_286_, v___x_341_);
v___x_343_ = lean_box(0);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_343_);
v___x_345_ = v___x_317_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_353_, lean_object* v_data_354_, lean_object* v_ref_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_353_, v_data_354_, v_ref_355_, v_msg_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_361_){
_start:
{
if (lean_obj_tag(v_e_361_) == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 2;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_364_);
lean_dec_ref(v_e_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_370_; double v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(1000u);
v___x_371_ = lean_float_of_nat(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_372_, uint8_t v_collapsed_373_, lean_object* v_tag_374_, lean_object* v_opts_375_, uint8_t v_clsEnabled_376_, lean_object* v_oldTraces_377_, lean_object* v_msg_378_, lean_object* v_resStartStop_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_fst_383_; lean_object* v_snd_384_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v_data_388_; lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___y_396_; lean_object* v_a_397_; uint8_t v___y_412_; double v___y_443_; 
v_fst_383_ = lean_ctor_get(v_resStartStop_379_, 0);
lean_inc(v_fst_383_);
v_snd_384_ = lean_ctor_get(v_resStartStop_379_, 1);
lean_inc(v_snd_384_);
lean_dec_ref(v_resStartStop_379_);
v_fst_391_ = lean_ctor_get(v_snd_384_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_snd_384_, 1);
lean_inc(v_snd_392_);
lean_dec(v_snd_384_);
v___x_393_ = l_Lean_trace_profiler;
v___x_394_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_375_, v___x_393_);
if (v___x_394_ == 0)
{
v___y_412_ = v___x_394_;
goto v___jp_411_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = l_Lean_trace_profiler_useHeartbeats;
v___x_449_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_375_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; double v___x_452_; double v___x_453_; double v___x_454_; 
v___x_450_ = l_Lean_trace_profiler_threshold;
v___x_451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_375_, v___x_450_);
v___x_452_ = lean_float_of_nat(v___x_451_);
v___x_453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_454_ = lean_float_div(v___x_452_, v___x_453_);
v___y_443_ = v___x_454_;
goto v___jp_442_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; 
v___x_455_ = l_Lean_trace_profiler_threshold;
v___x_456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_375_, v___x_455_);
v___x_457_ = lean_float_of_nat(v___x_456_);
v___y_443_ = v___x_457_;
goto v___jp_442_;
}
}
v___jp_385_:
{
lean_object* v___x_389_; 
lean_inc(v___y_386_);
v___x_389_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_377_, v_data_388_, v___y_386_, v___y_387_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref_known(v___x_389_, 1);
v___x_390_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_383_);
return v___x_390_;
}
else
{
lean_dec(v_fst_383_);
return v___x_389_;
}
}
v___jp_395_:
{
uint8_t v_result_398_; lean_object* v___x_399_; lean_object* v___x_400_; double v___x_401_; lean_object* v_data_402_; 
v_result_398_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_383_);
v___x_399_ = lean_box(v_result_398_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
v___x_401_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_374_);
lean_inc_ref(v___x_400_);
lean_inc(v_cls_372_);
v_data_402_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_402_, 0, v_cls_372_);
lean_ctor_set(v_data_402_, 1, v___x_400_);
lean_ctor_set(v_data_402_, 2, v_tag_374_);
lean_ctor_set_float(v_data_402_, sizeof(void*)*3, v___x_401_);
lean_ctor_set_float(v_data_402_, sizeof(void*)*3 + 8, v___x_401_);
lean_ctor_set_uint8(v_data_402_, sizeof(void*)*3 + 16, v_collapsed_373_);
if (v___x_394_ == 0)
{
lean_dec_ref_known(v___x_400_, 1);
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
lean_dec_ref(v_tag_374_);
lean_dec(v_cls_372_);
v___y_386_ = v___y_396_;
v___y_387_ = v_a_397_;
v_data_388_ = v_data_402_;
goto v___jp_385_;
}
else
{
lean_object* v_data_403_; double v___x_404_; double v___x_405_; 
lean_dec_ref_known(v_data_402_, 3);
v_data_403_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_403_, 0, v_cls_372_);
lean_ctor_set(v_data_403_, 1, v___x_400_);
lean_ctor_set(v_data_403_, 2, v_tag_374_);
v___x_404_ = lean_unbox_float(v_fst_391_);
lean_dec(v_fst_391_);
lean_ctor_set_float(v_data_403_, sizeof(void*)*3, v___x_404_);
v___x_405_ = lean_unbox_float(v_snd_392_);
lean_dec(v_snd_392_);
lean_ctor_set_float(v_data_403_, sizeof(void*)*3 + 8, v___x_405_);
lean_ctor_set_uint8(v_data_403_, sizeof(void*)*3 + 16, v_collapsed_373_);
v___y_386_ = v___y_396_;
v___y_387_ = v_a_397_;
v_data_388_ = v_data_403_;
goto v___jp_385_;
}
}
v___jp_406_:
{
lean_object* v_ref_407_; lean_object* v___x_408_; 
v_ref_407_ = lean_ctor_get(v___y_380_, 5);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v_fst_383_);
v___x_408_ = lean_apply_4(v_msg_378_, v_fst_383_, v___y_380_, v___y_381_, lean_box(0));
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v___y_396_ = v_ref_407_;
v_a_397_ = v_a_409_;
goto v___jp_395_;
}
else
{
lean_object* v___x_410_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_396_ = v_ref_407_;
v_a_397_ = v___x_410_;
goto v___jp_395_;
}
}
v___jp_411_:
{
if (v_clsEnabled_376_ == 0)
{
if (v___y_412_ == 0)
{
lean_object* v___x_413_; lean_object* v_traceState_414_; lean_object* v_env_415_; lean_object* v_nextMacroScope_416_; lean_object* v_ngen_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_cache_419_; lean_object* v_messages_420_; lean_object* v_infoState_421_; lean_object* v_snapshotTasks_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
lean_dec_ref(v_msg_378_);
lean_dec_ref(v_tag_374_);
lean_dec(v_cls_372_);
v___x_413_ = lean_st_ref_take(v___y_381_);
v_traceState_414_ = lean_ctor_get(v___x_413_, 4);
v_env_415_ = lean_ctor_get(v___x_413_, 0);
v_nextMacroScope_416_ = lean_ctor_get(v___x_413_, 1);
v_ngen_417_ = lean_ctor_get(v___x_413_, 2);
v_auxDeclNGen_418_ = lean_ctor_get(v___x_413_, 3);
v_cache_419_ = lean_ctor_get(v___x_413_, 5);
v_messages_420_ = lean_ctor_get(v___x_413_, 6);
v_infoState_421_ = lean_ctor_get(v___x_413_, 7);
v_snapshotTasks_422_ = lean_ctor_get(v___x_413_, 8);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_441_ == 0)
{
v___x_424_ = v___x_413_;
v_isShared_425_ = v_isSharedCheck_441_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snapshotTasks_422_);
lean_inc(v_infoState_421_);
lean_inc(v_messages_420_);
lean_inc(v_cache_419_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_418_);
lean_inc(v_ngen_417_);
lean_inc(v_nextMacroScope_416_);
lean_inc(v_env_415_);
lean_dec(v___x_413_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_441_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint64_t v_tid_426_; lean_object* v_traces_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_440_; 
v_tid_426_ = lean_ctor_get_uint64(v_traceState_414_, sizeof(void*)*1);
v_traces_427_ = lean_ctor_get(v_traceState_414_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_traceState_414_);
if (v_isSharedCheck_440_ == 0)
{
v___x_429_ = v_traceState_414_;
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_traces_427_);
lean_dec(v_traceState_414_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_377_, v_traces_427_);
lean_dec_ref(v_traces_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_431_);
lean_ctor_set_uint64(v_reuseFailAlloc_439_, sizeof(void*)*1, v_tid_426_);
v___x_433_ = v_reuseFailAlloc_439_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v___x_433_);
v___x_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_env_415_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_nextMacroScope_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_ngen_417_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_auxDeclNGen_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_cache_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_messages_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_infoState_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_snapshotTasks_422_);
v___x_435_ = v_reuseFailAlloc_438_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_st_ref_set(v___y_381_, v___x_435_);
v___x_437_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_383_);
return v___x_437_;
}
}
}
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
v___jp_442_:
{
double v___x_444_; double v___x_445_; double v___x_446_; uint8_t v___x_447_; 
v___x_444_ = lean_unbox_float(v_snd_392_);
v___x_445_ = lean_unbox_float(v_fst_391_);
v___x_446_ = lean_float_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_float_decLt(v___y_443_, v___x_446_);
v___y_412_ = v___x_447_;
goto v___jp_411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_458_, lean_object* v_collapsed_459_, lean_object* v_tag_460_, lean_object* v_opts_461_, lean_object* v_clsEnabled_462_, lean_object* v_oldTraces_463_, lean_object* v_msg_464_, lean_object* v_resStartStop_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_collapsed_boxed_469_; uint8_t v_clsEnabled_boxed_470_; lean_object* v_res_471_; 
v_collapsed_boxed_469_ = lean_unbox(v_collapsed_459_);
v_clsEnabled_boxed_470_ = lean_unbox(v_clsEnabled_462_);
v_res_471_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_458_, v_collapsed_boxed_469_, v_tag_460_, v_opts_461_, v_clsEnabled_boxed_470_, v_oldTraces_463_, v_msg_464_, v_resStartStop_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec_ref(v_opts_461_);
return v_res_471_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_472_; double v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1000000000u);
v___x_473_ = lean_float_of_nat(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_487_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_488_ = l_Lean_Name_append(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_493_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_494_ = l_Lean_Name_append(v___x_493_, v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_516_, lean_object* v_s_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___y_522_; lean_object* v___y_523_; uint8_t v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v_a_532_; lean_object* v___y_542_; uint8_t v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v_a_552_; lean_object* v___y_555_; uint8_t v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_a_565_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint8_t v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_582_; lean_object* v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v_a_592_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v_a_615_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v_a_628_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v_element_722_; lean_object* v_children_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_891_; 
v_element_722_ = lean_ctor_get(v_s_517_, 0);
v_children_723_ = lean_ctor_get(v_s_517_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_s_517_);
if (v_isSharedCheck_891_ == 0)
{
v___x_725_ = v_s_517_;
v_isShared_726_ = v_isSharedCheck_891_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_children_723_);
lean_inc(v_element_722_);
lean_dec(v_s_517_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_891_;
goto v_resetjp_724_;
}
v___jp_521_:
{
lean_object* v___x_533_; double v___x_534_; double v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_533_ = lean_io_get_num_heartbeats();
v___x_534_ = lean_float_of_nat(v___y_522_);
v___x_535_ = lean_float_of_nat(v___x_533_);
v___x_536_ = lean_box_float(v___x_534_);
v___x_537_ = lean_box_float(v___x_535_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_a_532_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_530_);
v___x_540_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_530_, v___y_524_, v___y_529_, v___y_525_, v___y_527_, v___y_526_, v___y_523_, v___x_539_, v___y_531_, v___y_528_);
return v___x_540_;
}
v___jp_541_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_a_552_);
v___y_522_ = v___y_542_;
v___y_523_ = v___y_544_;
v___y_524_ = v___y_543_;
v___y_525_ = v___y_545_;
v___y_526_ = v___y_546_;
v___y_527_ = v___y_547_;
v___y_528_ = v___y_548_;
v___y_529_ = v___y_550_;
v___y_530_ = v___y_549_;
v___y_531_ = v___y_551_;
v_a_532_ = v___x_553_;
goto v___jp_521_;
}
v___jp_554_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_a_565_);
v___y_522_ = v___y_555_;
v___y_523_ = v___y_557_;
v___y_524_ = v___y_556_;
v___y_525_ = v___y_558_;
v___y_526_ = v___y_559_;
v___y_527_ = v___y_560_;
v___y_528_ = v___y_561_;
v___y_529_ = v___y_563_;
v___y_530_ = v___y_562_;
v___y_531_ = v___y_564_;
v_a_532_ = v___x_566_;
goto v___jp_521_;
}
v___jp_567_:
{
if (lean_obj_tag(v___y_578_) == 0)
{
lean_object* v_a_579_; 
v_a_579_ = lean_ctor_get(v___y_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___y_578_, 1);
v___y_542_ = v___y_568_;
v___y_543_ = v___y_570_;
v___y_544_ = v___y_569_;
v___y_545_ = v___y_571_;
v___y_546_ = v___y_572_;
v___y_547_ = v___y_573_;
v___y_548_ = v___y_574_;
v___y_549_ = v___y_576_;
v___y_550_ = v___y_575_;
v___y_551_ = v___y_577_;
v_a_552_ = v_a_579_;
goto v___jp_541_;
}
else
{
lean_object* v_a_580_; 
v_a_580_ = lean_ctor_get(v___y_578_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___y_578_, 1);
v___y_555_ = v___y_568_;
v___y_556_ = v___y_570_;
v___y_557_ = v___y_569_;
v___y_558_ = v___y_571_;
v___y_559_ = v___y_572_;
v___y_560_ = v___y_573_;
v___y_561_ = v___y_574_;
v___y_562_ = v___y_576_;
v___y_563_ = v___y_575_;
v___y_564_ = v___y_577_;
v_a_565_ = v_a_580_;
goto v___jp_554_;
}
}
v___jp_581_:
{
lean_object* v___x_593_; double v___x_594_; double v___x_595_; double v___x_596_; double v___x_597_; double v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_593_ = lean_io_mono_nanos_now();
v___x_594_ = lean_float_of_nat(v___y_582_);
v___x_595_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_596_ = lean_float_div(v___x_594_, v___x_595_);
v___x_597_ = lean_float_of_nat(v___x_593_);
v___x_598_ = lean_float_div(v___x_597_, v___x_595_);
v___x_599_ = lean_box_float(v___x_596_);
v___x_600_ = lean_box_float(v___x_598_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_a_592_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_590_);
v___x_603_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_590_, v___y_584_, v___y_589_, v___y_585_, v___y_587_, v___y_586_, v___y_583_, v___x_602_, v___y_591_, v___y_588_);
return v___x_603_;
}
v___jp_604_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_a_615_);
v___y_582_ = v___y_605_;
v___y_583_ = v___y_607_;
v___y_584_ = v___y_606_;
v___y_585_ = v___y_608_;
v___y_586_ = v___y_609_;
v___y_587_ = v___y_610_;
v___y_588_ = v___y_611_;
v___y_589_ = v___y_613_;
v___y_590_ = v___y_612_;
v___y_591_ = v___y_614_;
v_a_592_ = v___x_616_;
goto v___jp_581_;
}
v___jp_617_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_a_628_);
v___y_582_ = v___y_618_;
v___y_583_ = v___y_620_;
v___y_584_ = v___y_619_;
v___y_585_ = v___y_621_;
v___y_586_ = v___y_622_;
v___y_587_ = v___y_623_;
v___y_588_ = v___y_624_;
v___y_589_ = v___y_626_;
v___y_590_ = v___y_625_;
v___y_591_ = v___y_627_;
v_a_592_ = v___x_629_;
goto v___jp_581_;
}
v___jp_630_:
{
if (lean_obj_tag(v___y_641_) == 0)
{
lean_object* v_a_642_; 
v_a_642_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___y_641_, 1);
v___y_605_ = v___y_631_;
v___y_606_ = v___y_633_;
v___y_607_ = v___y_632_;
v___y_608_ = v___y_634_;
v___y_609_ = v___y_635_;
v___y_610_ = v___y_636_;
v___y_611_ = v___y_637_;
v___y_612_ = v___y_639_;
v___y_613_ = v___y_638_;
v___y_614_ = v___y_640_;
v_a_615_ = v_a_642_;
goto v___jp_604_;
}
else
{
lean_object* v_a_643_; 
v_a_643_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___y_641_, 1);
v___y_618_ = v___y_631_;
v___y_619_ = v___y_633_;
v___y_620_ = v___y_632_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_635_;
v___y_623_ = v___y_636_;
v___y_624_ = v___y_637_;
v___y_625_ = v___y_639_;
v___y_626_ = v___y_638_;
v___y_627_ = v___y_640_;
v_a_628_ = v_a_643_;
goto v___jp_617_;
}
}
v___jp_644_:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_654_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_trace_profiler_useHeartbeats;
v___x_661_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_652_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_io_mono_nanos_now();
v___x_663_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_657_, v___y_649_, v___y_654_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
if (lean_obj_tag(v___y_647_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_val_664_ = lean_ctor_get(v___y_647_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___y_647_, 1);
v___x_665_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_648_);
v___x_666_ = l_Lean_Name_mkStr2(v___y_648_, v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_666_);
v___x_668_ = l_Lean_Name_append(v___x_667_, v___x_666_);
v___x_669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_650_, v___y_652_, v___x_668_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_666_);
lean_dec(v_val_664_);
v___x_670_ = lean_box(0);
v___y_605_ = v___x_662_;
v___y_606_ = v___y_646_;
v___y_607_ = v___y_645_;
v___y_608_ = v___y_652_;
v___y_609_ = v_a_659_;
v___y_610_ = v___y_653_;
v___y_611_ = v___y_654_;
v___y_612_ = v___y_656_;
v___y_613_ = v___y_655_;
v___y_614_ = v___y_649_;
v_a_615_ = v___x_670_;
goto v___jp_604_;
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
v___x_675_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_666_, v___x_674_, v___y_649_, v___y_654_);
v___y_631_ = v___x_662_;
v___y_632_ = v___y_645_;
v___y_633_ = v___y_646_;
v___y_634_ = v___y_652_;
v___y_635_ = v_a_659_;
v___y_636_ = v___y_653_;
v___y_637_ = v___y_654_;
v___y_638_ = v___y_655_;
v___y_639_ = v___y_656_;
v___y_640_ = v___y_649_;
v___y_641_ = v___x_675_;
goto v___jp_630_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_666_);
v_a_676_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_686_ == 0)
{
v___x_678_ = v___x_672_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_672_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_io_error_to_string(v_a_676_);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 3);
lean_ctor_set(v___x_678_, 0, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_685_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Lean_MessageData_ofFormat(v___x_682_);
lean_inc(v___y_651_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_651_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___y_618_ = v___x_662_;
v___y_619_ = v___y_646_;
v___y_620_ = v___y_645_;
v___y_621_ = v___y_652_;
v___y_622_ = v_a_659_;
v___y_623_ = v___y_653_;
v___y_624_ = v___y_654_;
v___y_625_ = v___y_656_;
v___y_626_ = v___y_655_;
v___y_627_ = v___y_649_;
v_a_628_ = v___x_684_;
goto v___jp_617_;
}
}
}
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v___y_647_);
v___x_687_ = lean_box(0);
v___y_605_ = v___x_662_;
v___y_606_ = v___y_646_;
v___y_607_ = v___y_645_;
v___y_608_ = v___y_652_;
v___y_609_ = v_a_659_;
v___y_610_ = v___y_653_;
v___y_611_ = v___y_654_;
v___y_612_ = v___y_656_;
v___y_613_ = v___y_655_;
v___y_614_ = v___y_649_;
v_a_615_ = v___x_687_;
goto v___jp_604_;
}
}
else
{
lean_dec(v___y_647_);
v___y_631_ = v___x_662_;
v___y_632_ = v___y_645_;
v___y_633_ = v___y_646_;
v___y_634_ = v___y_652_;
v___y_635_ = v_a_659_;
v___y_636_ = v___y_653_;
v___y_637_ = v___y_654_;
v___y_638_ = v___y_655_;
v___y_639_ = v___y_656_;
v___y_640_ = v___y_649_;
v___y_641_ = v___x_663_;
goto v___jp_630_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_io_get_num_heartbeats();
v___x_689_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_657_, v___y_649_, v___y_654_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec_ref_known(v___x_689_, 1);
if (lean_obj_tag(v___y_647_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_val_690_ = lean_ctor_get(v___y_647_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___y_647_, 1);
v___x_691_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_648_);
v___x_692_ = l_Lean_Name_mkStr2(v___y_648_, v___x_691_);
v___x_693_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_692_);
v___x_694_ = l_Lean_Name_append(v___x_693_, v___x_692_);
v___x_695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_650_, v___y_652_, v___x_694_);
lean_dec(v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v___x_692_);
lean_dec(v_val_690_);
v___x_696_ = lean_box(0);
v___y_542_ = v___x_688_;
v___y_543_ = v___y_646_;
v___y_544_ = v___y_645_;
v___y_545_ = v___y_652_;
v___y_546_ = v_a_659_;
v___y_547_ = v___y_653_;
v___y_548_ = v___y_654_;
v___y_549_ = v___y_656_;
v___y_550_ = v___y_655_;
v___y_551_ = v___y_649_;
v_a_552_ = v___x_696_;
goto v___jp_541_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = l_Lean_Elab_InfoTree_format(v_val_690_, v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = l_Lean_MessageData_ofFormat(v_a_699_);
v___x_701_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_692_, v___x_700_, v___y_649_, v___y_654_);
v___y_568_ = v___x_688_;
v___y_569_ = v___y_645_;
v___y_570_ = v___y_646_;
v___y_571_ = v___y_652_;
v___y_572_ = v_a_659_;
v___y_573_ = v___y_653_;
v___y_574_ = v___y_654_;
v___y_575_ = v___y_655_;
v___y_576_ = v___y_656_;
v___y_577_ = v___y_649_;
v___y_578_ = v___x_701_;
goto v___jp_567_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_712_; 
lean_dec(v___x_692_);
v_a_702_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_712_ == 0)
{
v___x_704_ = v___x_698_;
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_698_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_io_error_to_string(v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 3);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_711_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = l_Lean_MessageData_ofFormat(v___x_708_);
lean_inc(v___y_651_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___y_651_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___y_555_ = v___x_688_;
v___y_556_ = v___y_646_;
v___y_557_ = v___y_645_;
v___y_558_ = v___y_652_;
v___y_559_ = v_a_659_;
v___y_560_ = v___y_653_;
v___y_561_ = v___y_654_;
v___y_562_ = v___y_656_;
v___y_563_ = v___y_655_;
v___y_564_ = v___y_649_;
v_a_565_ = v___x_710_;
goto v___jp_554_;
}
}
}
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v___y_647_);
v___x_713_ = lean_box(0);
v___y_542_ = v___x_688_;
v___y_543_ = v___y_646_;
v___y_544_ = v___y_645_;
v___y_545_ = v___y_652_;
v___y_546_ = v_a_659_;
v___y_547_ = v___y_653_;
v___y_548_ = v___y_654_;
v___y_549_ = v___y_656_;
v___y_550_ = v___y_655_;
v___y_551_ = v___y_649_;
v_a_552_ = v___x_713_;
goto v___jp_541_;
}
}
else
{
lean_dec(v___y_647_);
v___y_568_ = v___x_688_;
v___y_569_ = v___y_645_;
v___y_570_ = v___y_646_;
v___y_571_ = v___y_652_;
v___y_572_ = v_a_659_;
v___y_573_ = v___y_653_;
v___y_574_ = v___y_654_;
v___y_575_ = v___y_655_;
v___y_576_ = v___y_656_;
v___y_577_ = v___y_649_;
v___y_578_ = v___x_689_;
goto v___jp_567_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v___y_657_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_645_);
v_a_714_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_658_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_658_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
v_resetjp_724_:
{
lean_object* v_desc_727_; lean_object* v_diagnostics_728_; lean_object* v_infoTree_x3f_729_; lean_object* v_desc_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___x_827_; 
v_desc_727_ = lean_ctor_get(v_element_722_, 0);
lean_inc_ref(v_desc_727_);
v_diagnostics_728_ = lean_ctor_get(v_element_722_, 1);
lean_inc_ref(v_diagnostics_728_);
v_infoTree_x3f_729_ = lean_ctor_get(v_element_722_, 2);
lean_inc(v_infoTree_x3f_729_);
lean_dec_ref(v_element_722_);
v___x_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_827_, 0, v_desc_727_);
switch(lean_obj_tag(v_range_x3f_516_))
{
case 0:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v_desc_731_ = v___x_829_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
goto v___jp_730_;
}
case 1:
{
lean_object* v_range_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_888_; 
v_range_830_ = lean_ctor_get(v_range_x3f_516_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_range_x3f_516_);
if (v_isSharedCheck_888_ == 0)
{
v___x_832_ = v_range_x3f_516_;
v_isShared_833_ = v_isSharedCheck_888_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_range_830_);
lean_dec(v_range_x3f_516_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_888_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_fileMap_834_; lean_object* v_start_835_; lean_object* v_stop_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_887_; 
v_fileMap_834_ = lean_ctor_get(v_a_518_, 1);
v_start_835_ = lean_ctor_get(v_range_830_, 0);
v_stop_836_ = lean_ctor_get(v_range_830_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_range_830_);
if (v_isSharedCheck_887_ == 0)
{
v___x_838_ = v_range_830_;
v_isShared_839_ = v_isSharedCheck_887_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_stop_836_);
lean_inc(v_start_835_);
lean_dec(v_range_830_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_887_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v_line_841_; lean_object* v_column_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_886_; 
lean_inc_ref(v_fileMap_834_);
v___x_840_ = l_Lean_FileMap_toPosition(v_fileMap_834_, v_start_835_);
lean_dec(v_start_835_);
v_line_841_ = lean_ctor_get(v___x_840_, 0);
v_column_842_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_886_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_886_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_column_842_);
lean_inc(v_line_841_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_886_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_line_847_; lean_object* v_column_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_885_; 
lean_inc_ref(v_fileMap_834_);
v___x_846_ = l_Lean_FileMap_toPosition(v_fileMap_834_, v_stop_836_);
lean_dec(v_stop_836_);
v_line_847_ = lean_ctor_get(v___x_846_, 0);
v_column_848_ = lean_ctor_get(v___x_846_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_885_ == 0)
{
v___x_850_ = v___x_846_;
v_isShared_851_ = v_isSharedCheck_885_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_column_848_);
lean_inc(v_line_847_);
lean_dec(v___x_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_885_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_853_ = l_Nat_reprFast(v_line_841_);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 3);
lean_ctor_set(v___x_832_, 0, v___x_853_);
v___x_855_ = v___x_832_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_884_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 5);
lean_ctor_set(v___x_850_, 1, v___x_855_);
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_883_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 5);
lean_ctor_set(v___x_844_, 1, v___x_858_);
lean_ctor_set(v___x_844_, 0, v___x_857_);
v___x_860_ = v___x_844_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_882_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = l_Nat_reprFast(v_column_842_);
v___x_862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 5);
lean_ctor_set(v___x_838_, 1, v___x_862_);
lean_ctor_set(v___x_838_, 0, v___x_860_);
v___x_864_ = v___x_838_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_881_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Nat_reprFast(v_line_847_);
v___x_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_852_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_858_);
v___x_873_ = l_Nat_reprFast(v_column_848_);
v___x_874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_872_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_865_);
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_868_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_827_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v_desc_731_ = v___x_880_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
goto v___jp_730_;
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
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_827_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v_desc_731_ = v___x_890_;
v___y_732_ = v_a_518_;
v___y_733_ = v_a_519_;
goto v___jp_730_;
}
}
v___jp_730_:
{
lean_object* v_msgLog_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_825_; 
v_msgLog_734_ = lean_ctor_get(v_diagnostics_728_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_diagnostics_728_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_diagnostics_728_, 1);
lean_dec(v_unused_826_);
v___x_736_ = v_diagnostics_728_;
v_isShared_737_ = v_isSharedCheck_825_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_msgLog_734_);
lean_dec(v_diagnostics_728_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_825_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = l_Lean_MessageLog_toList(v_msgLog_734_);
lean_dec_ref(v_msgLog_734_);
v___x_739_ = lean_box(0);
v___x_740_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_738_, v___x_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_options_741_; lean_object* v_a_742_; lean_object* v_ref_743_; lean_object* v_inheritedTraceOptions_744_; uint8_t v_hasTrace_745_; lean_object* v___x_746_; 
v_options_741_ = lean_ctor_get(v___y_732_, 2);
v_a_742_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_740_, 1);
v_ref_743_ = lean_ctor_get(v___y_732_, 5);
v_inheritedTraceOptions_744_ = lean_ctor_get(v___y_732_, 13);
v_hasTrace_745_ = lean_ctor_get_uint8(v_options_741_, sizeof(void*)*1);
v___x_746_ = lean_array_to_list(v_children_723_);
if (v_hasTrace_745_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_a_742_);
lean_del_object(v___x_736_);
lean_dec(v_desc_731_);
lean_del_object(v___x_725_);
v___x_747_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_746_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_759_; 
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_747_, 0);
lean_dec(v_unused_760_);
v___x_749_ = v___x_747_;
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
else
{
lean_dec(v___x_747_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
if (lean_obj_tag(v_infoTree_x3f_729_) == 1)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec_ref_known(v_infoTree_x3f_729_, 1);
v___x_751_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
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
else
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v_infoTree_x3f_729_);
v___x_755_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_755_);
v___x_757_ = v___x_749_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_729_);
return v___x_747_;
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_762_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_763_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_762_, v_a_742_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 5);
lean_ctor_set(v___x_736_, 1, v___x_763_);
lean_ctor_set(v___x_736_, 0, v_desc_731_);
v___x_765_ = v___x_736_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_desc_731_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_816_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___f_766_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_766_, 0, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_768_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_769_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_744_, v_options_741_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = l_Lean_trace_profiler;
v___x_772_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_741_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v___f_766_);
v___x_773_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_746_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_814_; 
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_815_);
v___x_775_ = v___x_773_;
v_isShared_776_ = v_isSharedCheck_814_;
goto v_resetjp_774_;
}
else
{
lean_dec(v___x_773_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_814_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
if (lean_obj_tag(v_infoTree_x3f_729_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_809_; 
v_val_777_ = lean_ctor_get(v_infoTree_x3f_729_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_infoTree_x3f_729_);
if (v_isSharedCheck_809_ == 0)
{
v___x_779_ = v_infoTree_x3f_729_;
v_isShared_780_ = v_isSharedCheck_809_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v_infoTree_x3f_729_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_809_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_782_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_744_, v_options_741_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_del_object(v___x_779_);
lean_dec(v_val_777_);
lean_del_object(v___x_725_);
v___x_784_ = lean_box(0);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_784_);
v___x_786_ = v___x_775_;
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
else
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_775_);
v___x_788_ = lean_box(0);
v___x_789_ = l_Lean_Elab_InfoTree_format(v_val_777_, v___x_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_del_object(v___x_779_);
lean_del_object(v___x_725_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = l_Lean_MessageData_ofFormat(v_a_790_);
v___x_792_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_781_, v___x_791_, v___y_732_, v___y_733_);
return v___x_792_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_808_; 
v_a_793_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_808_ == 0)
{
v___x_795_ = v___x_789_;
v_isShared_796_ = v_isSharedCheck_808_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_808_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_io_error_to_string(v_a_793_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 3);
lean_ctor_set(v___x_779_, 0, v___x_797_);
v___x_799_ = v___x_779_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_807_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = l_Lean_MessageData_ofFormat(v___x_799_);
lean_inc(v_ref_743_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_800_);
lean_ctor_set(v___x_725_, 0, v_ref_743_);
v___x_802_ = v___x_725_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_ref_743_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_802_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
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
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_infoTree_x3f_729_);
lean_del_object(v___x_725_);
v___x_810_ = lean_box(0);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_810_);
v___x_812_ = v___x_775_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_729_);
lean_del_object(v___x_725_);
return v___x_773_;
}
}
else
{
lean_del_object(v___x_725_);
v___y_645_ = v___f_766_;
v___y_646_ = v_hasTrace_745_;
v___y_647_ = v_infoTree_x3f_729_;
v___y_648_ = v___x_761_;
v___y_649_ = v___y_732_;
v___y_650_ = v_inheritedTraceOptions_744_;
v___y_651_ = v_ref_743_;
v___y_652_ = v_options_741_;
v___y_653_ = v___x_770_;
v___y_654_ = v___y_733_;
v___y_655_ = v___x_768_;
v___y_656_ = v___x_767_;
v___y_657_ = v___x_746_;
goto v___jp_644_;
}
}
else
{
lean_del_object(v___x_725_);
v___y_645_ = v___f_766_;
v___y_646_ = v_hasTrace_745_;
v___y_647_ = v_infoTree_x3f_729_;
v___y_648_ = v___x_761_;
v___y_649_ = v___y_732_;
v___y_650_ = v_inheritedTraceOptions_744_;
v___y_651_ = v_ref_743_;
v___y_652_ = v_options_741_;
v___y_653_ = v___x_770_;
v___y_654_ = v___y_733_;
v___y_655_ = v___x_768_;
v___y_656_ = v___x_767_;
v___y_657_ = v___x_746_;
goto v___jp_644_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_del_object(v___x_736_);
lean_dec(v_desc_731_);
lean_dec(v_infoTree_x3f_729_);
lean_del_object(v___x_725_);
lean_dec_ref(v_children_723_);
v_a_817_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_740_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_740_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
if (lean_obj_tag(v_as_892_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_head_898_; lean_object* v_tail_899_; lean_object* v_reportingRange_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_head_898_ = lean_ctor_get(v_as_892_, 0);
lean_inc(v_head_898_);
v_tail_899_ = lean_ctor_get(v_as_892_, 1);
lean_inc(v_tail_899_);
lean_dec_ref_known(v_as_892_, 2);
v_reportingRange_900_ = lean_ctor_get(v_head_898_, 1);
lean_inc(v_reportingRange_900_);
v___x_901_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_898_);
v___x_902_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_900_, v___x_901_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref_known(v___x_902_, 1);
v_as_892_ = v_tail_899_;
goto _start;
}
else
{
lean_dec(v_tail_899_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_909_, lean_object* v_s_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_909_, v_s_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_915_, v_x_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_921_, v_x_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_928_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_933_, v_x_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_box(2);
v___x_944_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_943_, v_s_939_, v_a_940_, v_a_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Language_SnapshotTree_trace(v_s_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_949_;
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

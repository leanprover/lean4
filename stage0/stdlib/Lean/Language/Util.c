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
lean_object* v___x_106_; lean_object* v_toCold_107_; lean_object* v_env_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_toCold_107_ = lean_ctor_get(v___y_103_, 0);
v_env_108_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_106_);
v_options_109_ = lean_ctor_get(v_toCold_107_, 2);
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_111_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_109_);
v___x_112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_112_, 0, v_env_108_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
lean_ctor_set(v___x_112_, 2, v___x_111_);
lean_ctor_set(v___x_112_, 3, v_options_109_);
v___x_113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_msgData_102_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_119_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_120_; double v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_float_of_nat(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_125_, lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_ref_130_; lean_object* v___x_131_; lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_177_; 
v_ref_130_ = lean_ctor_get(v___y_127_, 2);
v___x_131_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_126_, v___y_127_, v___y_128_);
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_177_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_177_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_177_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v_traceState_137_; lean_object* v_env_138_; lean_object* v_nextMacroScope_139_; lean_object* v_ngen_140_; lean_object* v_auxDeclNGen_141_; lean_object* v_cache_142_; lean_object* v_recordedDeps_143_; lean_object* v_messages_144_; lean_object* v_infoState_145_; lean_object* v_snapshotTasks_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_176_; 
v___x_136_ = lean_st_ref_take(v___y_128_);
v_traceState_137_ = lean_ctor_get(v___x_136_, 4);
v_env_138_ = lean_ctor_get(v___x_136_, 0);
v_nextMacroScope_139_ = lean_ctor_get(v___x_136_, 1);
v_ngen_140_ = lean_ctor_get(v___x_136_, 2);
v_auxDeclNGen_141_ = lean_ctor_get(v___x_136_, 3);
v_cache_142_ = lean_ctor_get(v___x_136_, 5);
v_recordedDeps_143_ = lean_ctor_get(v___x_136_, 6);
v_messages_144_ = lean_ctor_get(v___x_136_, 7);
v_infoState_145_ = lean_ctor_get(v___x_136_, 8);
v_snapshotTasks_146_ = lean_ctor_get(v___x_136_, 9);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_176_ == 0)
{
v___x_148_ = v___x_136_;
v_isShared_149_ = v_isSharedCheck_176_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snapshotTasks_146_);
lean_inc(v_infoState_145_);
lean_inc(v_messages_144_);
lean_inc(v_recordedDeps_143_);
lean_inc(v_cache_142_);
lean_inc(v_traceState_137_);
lean_inc(v_auxDeclNGen_141_);
lean_inc(v_ngen_140_);
lean_inc(v_nextMacroScope_139_);
lean_inc(v_env_138_);
lean_dec(v___x_136_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_176_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint64_t v_tid_150_; lean_object* v_traces_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_175_; 
v_tid_150_ = lean_ctor_get_uint64(v_traceState_137_, sizeof(void*)*1);
v_traces_151_ = lean_ctor_get(v_traceState_137_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_traceState_137_);
if (v_isSharedCheck_175_ == 0)
{
v___x_153_ = v_traceState_137_;
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_traces_151_);
lean_dec(v_traceState_137_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; double v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_155_ = lean_box(0);
v___x_156_ = lean_box(0);
v___x_157_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_158_ = 0;
v___x_159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_160_, 0, v_cls_125_);
lean_ctor_set(v___x_160_, 1, v___x_156_);
lean_ctor_set(v___x_160_, 2, v___x_159_);
lean_ctor_set_float(v___x_160_, sizeof(void*)*3, v___x_157_);
lean_ctor_set_float(v___x_160_, sizeof(void*)*3 + 8, v___x_157_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*3 + 16, v___x_158_);
v___x_161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_162_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v_a_132_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
lean_inc(v_ref_130_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_ref_130_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Lean_PersistentArray_push___redArg(v_traces_151_, v___x_163_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_164_);
v___x_166_ = v___x_153_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_164_);
lean_ctor_set_uint64(v_reuseFailAlloc_174_, sizeof(void*)*1, v_tid_150_);
v___x_166_ = v_reuseFailAlloc_174_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 4, v___x_166_);
v___x_168_ = v___x_148_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_env_138_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_nextMacroScope_139_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_ngen_140_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_auxDeclNGen_141_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v_cache_142_);
lean_ctor_set(v_reuseFailAlloc_173_, 6, v_recordedDeps_143_);
lean_ctor_set(v_reuseFailAlloc_173_, 7, v_messages_144_);
lean_ctor_set(v_reuseFailAlloc_173_, 8, v_infoState_145_);
lean_ctor_set(v_reuseFailAlloc_173_, 9, v_snapshotTasks_146_);
v___x_168_ = v_reuseFailAlloc_173_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_st_ref_put(v___y_128_, v___x_168_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_155_);
v___x_171_ = v___x_134_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_155_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_178_, lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_178_, v_msg_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_dec(v_pre_184_);
return v_x_185_;
}
else
{
lean_object* v_head_187_; lean_object* v_tail_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_198_; 
v_head_187_ = lean_ctor_get(v_x_186_, 0);
v_tail_188_ = lean_ctor_get(v_x_186_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_198_ == 0)
{
v___x_190_ = v_x_186_;
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_tail_188_);
lean_inc(v_head_187_);
lean_dec(v_x_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
lean_inc(v_pre_184_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 5);
lean_ctor_set(v___x_190_, 1, v_pre_184_);
lean_ctor_set(v___x_190_, 0, v_x_185_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_x_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_pre_184_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_194_, 0, v_head_187_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v_x_185_ = v___x_195_;
v_x_186_ = v_tail_188_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v___x_201_; 
lean_dec(v_pre_199_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v_head_202_; lean_object* v_tail_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
v_head_202_ = lean_ctor_get(v_x_200_, 0);
v_tail_203_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v_x_200_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_tail_203_);
lean_inc(v_head_202_);
lean_dec(v_x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_207_, 0, v_head_202_);
lean_inc(v_pre_199_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 5);
lean_ctor_set(v___x_205_, 1, v___x_207_);
lean_ctor_set(v___x_205_, 0, v_pre_199_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_pre_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_199_, v___x_209_, v_tail_203_);
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_List_reverse___redArg(v_x_214_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v_head_218_; lean_object* v_tail_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_head_218_ = lean_ctor_get(v_x_213_, 0);
v_tail_219_ = lean_ctor_get(v_x_213_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_229_ == 0)
{
v___x_221_ = v_x_213_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_tail_219_);
lean_inc(v_head_218_);
lean_dec(v_x_213_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_223_ = 0;
v___x_224_ = l_Lean_Message_toString(v_head_218_, v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v_x_214_);
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_x_214_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v_x_213_ = v_tail_219_;
v_x_214_ = v___x_226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_230_, v_x_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_a_236_ = lean_ctor_get(v_x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v_x_234_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v_x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 1);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v_x_234_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v_x_234_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v_x_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_255_, lean_object* v_opt_256_){
_start:
{
lean_object* v_name_257_; lean_object* v_defValue_258_; lean_object* v_map_259_; lean_object* v___x_260_; 
v_name_257_ = lean_ctor_get(v_opt_256_, 0);
v_defValue_258_ = lean_ctor_get(v_opt_256_, 1);
v_map_259_ = lean_ctor_get(v_opts_255_, 0);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_259_, v_name_257_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_inc(v_defValue_258_);
return v_defValue_258_;
}
else
{
lean_object* v_val_261_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_260_, 1);
if (lean_obj_tag(v_val_261_) == 3)
{
lean_object* v_v_262_; 
v_v_262_ = lean_ctor_get(v_val_261_, 0);
lean_inc(v_v_262_);
lean_dec_ref_known(v_val_261_, 1);
return v_v_262_;
}
else
{
lean_dec(v_val_261_);
lean_inc(v_defValue_258_);
return v_defValue_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_263_, lean_object* v_opt_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_263_, v_opt_264_);
lean_dec_ref(v_opt_264_);
lean_dec_ref(v_opts_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_266_, size_t v_i_267_, lean_object* v_bs_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_269_ == 0)
{
return v_bs_268_;
}
else
{
lean_object* v_v_270_; lean_object* v_msg_271_; lean_object* v___x_272_; lean_object* v_bs_x27_273_; size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v_v_270_ = lean_array_uget_borrowed(v_bs_268_, v_i_267_);
v_msg_271_ = lean_ctor_get(v_v_270_, 1);
lean_inc_ref(v_msg_271_);
v___x_272_ = lean_unsigned_to_nat(0u);
v_bs_x27_273_ = lean_array_uset(v_bs_268_, v_i_267_, v___x_272_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_add(v_i_267_, v___x_274_);
v___x_276_ = lean_array_uset(v_bs_x27_273_, v_i_267_, v_msg_271_);
v_i_267_ = v___x_275_;
v_bs_268_ = v___x_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_278_, lean_object* v_i_279_, lean_object* v_bs_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_i_boxed_282_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_281_, v_i_boxed_282_, v_bs_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_284_, lean_object* v_data_285_, lean_object* v_ref_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_toCold_291_; lean_object* v_currRecDepth_292_; lean_object* v_ref_293_; uint16_t v_optionFlags_294_; uint8_t v_suppressElabErrors_295_; uint8_t v_isRecordingDeps_296_; lean_object* v_ref_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_traceState_300_; lean_object* v_traces_301_; lean_object* v___x_302_; size_t v_sz_303_; size_t v___x_304_; lean_object* v___x_305_; lean_object* v_msg_306_; lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_346_; 
v_toCold_291_ = lean_ctor_get(v___y_288_, 0);
v_currRecDepth_292_ = lean_ctor_get(v___y_288_, 1);
v_ref_293_ = lean_ctor_get(v___y_288_, 2);
v_optionFlags_294_ = lean_ctor_get_uint16(v___y_288_, sizeof(void*)*3);
v_suppressElabErrors_295_ = lean_ctor_get_uint8(v___y_288_, sizeof(void*)*3 + 2);
v_isRecordingDeps_296_ = lean_ctor_get_uint8(v___y_288_, sizeof(void*)*3 + 3);
v_ref_297_ = l_Lean_replaceRef(v_ref_286_, v_ref_293_);
lean_inc(v_currRecDepth_292_);
lean_inc_ref(v_toCold_291_);
v___x_298_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_298_, 0, v_toCold_291_);
lean_ctor_set(v___x_298_, 1, v_currRecDepth_292_);
lean_ctor_set(v___x_298_, 2, v_ref_297_);
lean_ctor_set_uint16(v___x_298_, sizeof(void*)*3, v_optionFlags_294_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*3 + 2, v_suppressElabErrors_295_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*3 + 3, v_isRecordingDeps_296_);
v___x_299_ = lean_st_ref_get(v___y_289_);
v_traceState_300_ = lean_ctor_get(v___x_299_, 4);
lean_inc_ref(v_traceState_300_);
lean_dec(v___x_299_);
v_traces_301_ = lean_ctor_get(v_traceState_300_, 0);
lean_inc_ref(v_traces_301_);
lean_dec_ref(v_traceState_300_);
v___x_302_ = l_Lean_PersistentArray_toArray___redArg(v_traces_301_);
lean_dec_ref(v_traces_301_);
v_sz_303_ = lean_array_size(v___x_302_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_303_, v___x_304_, v___x_302_);
v_msg_306_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_306_, 0, v_data_285_);
lean_ctor_set(v_msg_306_, 1, v_msg_287_);
lean_ctor_set(v_msg_306_, 2, v___x_305_);
v___x_307_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_306_, v___x_298_, v___y_289_);
lean_dec_ref_known(v___x_298_, 3);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_346_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_346_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_346_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_traceState_313_; lean_object* v_env_314_; lean_object* v_nextMacroScope_315_; lean_object* v_ngen_316_; lean_object* v_auxDeclNGen_317_; lean_object* v_cache_318_; lean_object* v_recordedDeps_319_; lean_object* v_messages_320_; lean_object* v_infoState_321_; lean_object* v_snapshotTasks_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_345_; 
v___x_312_ = lean_st_ref_take(v___y_289_);
v_traceState_313_ = lean_ctor_get(v___x_312_, 4);
v_env_314_ = lean_ctor_get(v___x_312_, 0);
v_nextMacroScope_315_ = lean_ctor_get(v___x_312_, 1);
v_ngen_316_ = lean_ctor_get(v___x_312_, 2);
v_auxDeclNGen_317_ = lean_ctor_get(v___x_312_, 3);
v_cache_318_ = lean_ctor_get(v___x_312_, 5);
v_recordedDeps_319_ = lean_ctor_get(v___x_312_, 6);
v_messages_320_ = lean_ctor_get(v___x_312_, 7);
v_infoState_321_ = lean_ctor_get(v___x_312_, 8);
v_snapshotTasks_322_ = lean_ctor_get(v___x_312_, 9);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_345_ == 0)
{
v___x_324_ = v___x_312_;
v_isShared_325_ = v_isSharedCheck_345_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_snapshotTasks_322_);
lean_inc(v_infoState_321_);
lean_inc(v_messages_320_);
lean_inc(v_recordedDeps_319_);
lean_inc(v_cache_318_);
lean_inc(v_traceState_313_);
lean_inc(v_auxDeclNGen_317_);
lean_inc(v_ngen_316_);
lean_inc(v_nextMacroScope_315_);
lean_inc(v_env_314_);
lean_dec(v___x_312_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_345_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint64_t v_tid_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_343_; 
v_tid_326_ = lean_ctor_get_uint64(v_traceState_313_, sizeof(void*)*1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_traceState_313_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_traceState_313_, 0);
lean_dec(v_unused_344_);
v___x_328_ = v_traceState_313_;
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_traceState_313_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_ref_286_);
lean_ctor_set(v___x_331_, 1, v_a_308_);
v___x_332_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_284_, v___x_331_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_334_ = v___x_328_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_332_);
lean_ctor_set_uint64(v_reuseFailAlloc_342_, sizeof(void*)*1, v_tid_326_);
v___x_334_ = v_reuseFailAlloc_342_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_334_);
v___x_336_ = v___x_324_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_env_314_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_nextMacroScope_315_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_ngen_316_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_auxDeclNGen_317_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_341_, 5, v_cache_318_);
lean_ctor_set(v_reuseFailAlloc_341_, 6, v_recordedDeps_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 7, v_messages_320_);
lean_ctor_set(v_reuseFailAlloc_341_, 8, v_infoState_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 9, v_snapshotTasks_322_);
v___x_336_ = v_reuseFailAlloc_341_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_st_ref_put(v___y_289_, v___x_336_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_330_);
v___x_339_ = v___x_310_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_330_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_347_, lean_object* v_data_348_, lean_object* v_ref_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_347_, v_data_348_, v_ref_349_, v_msg_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_355_){
_start:
{
if (lean_obj_tag(v_e_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 2;
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_358_);
lean_dec_ref(v_e_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_364_; double v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(1000u);
v___x_365_ = lean_float_of_nat(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_366_, uint8_t v_collapsed_367_, lean_object* v_tag_368_, lean_object* v_opts_369_, uint8_t v_clsEnabled_370_, lean_object* v_oldTraces_371_, lean_object* v_msg_372_, lean_object* v_resStartStop_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v_data_382_; lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___y_390_; lean_object* v_a_391_; uint8_t v___y_406_; double v___y_438_; 
v_fst_377_ = lean_ctor_get(v_resStartStop_373_, 0);
lean_inc(v_fst_377_);
v_snd_378_ = lean_ctor_get(v_resStartStop_373_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v_resStartStop_373_);
v_fst_385_ = lean_ctor_get(v_snd_378_, 0);
lean_inc(v_fst_385_);
v_snd_386_ = lean_ctor_get(v_snd_378_, 1);
lean_inc(v_snd_386_);
lean_dec(v_snd_378_);
v___x_387_ = l_Lean_trace_profiler;
v___x_388_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_369_, v___x_387_);
if (v___x_388_ == 0)
{
v___y_406_ = v___x_388_;
goto v___jp_405_;
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = l_Lean_trace_profiler_useHeartbeats;
v___x_444_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_369_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; double v___x_447_; double v___x_448_; double v___x_449_; 
v___x_445_ = l_Lean_trace_profiler_threshold;
v___x_446_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_369_, v___x_445_);
v___x_447_ = lean_float_of_nat(v___x_446_);
v___x_448_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_449_ = lean_float_div(v___x_447_, v___x_448_);
v___y_438_ = v___x_449_;
goto v___jp_437_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; double v___x_452_; 
v___x_450_ = l_Lean_trace_profiler_threshold;
v___x_451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_369_, v___x_450_);
v___x_452_ = lean_float_of_nat(v___x_451_);
v___y_438_ = v___x_452_;
goto v___jp_437_;
}
}
v___jp_379_:
{
lean_object* v___x_383_; 
lean_inc(v___y_381_);
v___x_383_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_371_, v_data_382_, v___y_381_, v___y_380_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; 
lean_dec_ref_known(v___x_383_, 1);
v___x_384_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_377_);
return v___x_384_;
}
else
{
lean_dec(v_fst_377_);
return v___x_383_;
}
}
v___jp_389_:
{
uint8_t v_result_392_; lean_object* v___x_393_; lean_object* v___x_394_; double v___x_395_; lean_object* v_data_396_; 
v_result_392_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_377_);
v___x_393_ = lean_box(v_result_392_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___x_395_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_368_);
lean_inc_ref(v___x_394_);
lean_inc(v_cls_366_);
v_data_396_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_396_, 0, v_cls_366_);
lean_ctor_set(v_data_396_, 1, v___x_394_);
lean_ctor_set(v_data_396_, 2, v_tag_368_);
lean_ctor_set_float(v_data_396_, sizeof(void*)*3, v___x_395_);
lean_ctor_set_float(v_data_396_, sizeof(void*)*3 + 8, v___x_395_);
lean_ctor_set_uint8(v_data_396_, sizeof(void*)*3 + 16, v_collapsed_367_);
if (v___x_388_ == 0)
{
lean_dec_ref_known(v___x_394_, 1);
lean_dec(v_snd_386_);
lean_dec(v_fst_385_);
lean_dec_ref(v_tag_368_);
lean_dec(v_cls_366_);
v___y_380_ = v_a_391_;
v___y_381_ = v___y_390_;
v_data_382_ = v_data_396_;
goto v___jp_379_;
}
else
{
lean_object* v_data_397_; double v___x_398_; double v___x_399_; 
lean_dec_ref_known(v_data_396_, 3);
v_data_397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_397_, 0, v_cls_366_);
lean_ctor_set(v_data_397_, 1, v___x_394_);
lean_ctor_set(v_data_397_, 2, v_tag_368_);
v___x_398_ = lean_unbox_float(v_fst_385_);
lean_dec(v_fst_385_);
lean_ctor_set_float(v_data_397_, sizeof(void*)*3, v___x_398_);
v___x_399_ = lean_unbox_float(v_snd_386_);
lean_dec(v_snd_386_);
lean_ctor_set_float(v_data_397_, sizeof(void*)*3 + 8, v___x_399_);
lean_ctor_set_uint8(v_data_397_, sizeof(void*)*3 + 16, v_collapsed_367_);
v___y_380_ = v_a_391_;
v___y_381_ = v___y_390_;
v_data_382_ = v_data_397_;
goto v___jp_379_;
}
}
v___jp_400_:
{
lean_object* v_ref_401_; lean_object* v___x_402_; 
v_ref_401_ = lean_ctor_get(v___y_374_, 2);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v_fst_377_);
v___x_402_ = lean_apply_4(v_msg_372_, v_fst_377_, v___y_374_, v___y_375_, lean_box(0));
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___y_390_ = v_ref_401_;
v_a_391_ = v_a_403_;
goto v___jp_389_;
}
else
{
lean_object* v___x_404_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_390_ = v_ref_401_;
v_a_391_ = v___x_404_;
goto v___jp_389_;
}
}
v___jp_405_:
{
if (v_clsEnabled_370_ == 0)
{
if (v___y_406_ == 0)
{
lean_object* v___x_407_; lean_object* v_traceState_408_; lean_object* v_env_409_; lean_object* v_nextMacroScope_410_; lean_object* v_ngen_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_cache_413_; lean_object* v_recordedDeps_414_; lean_object* v_messages_415_; lean_object* v_infoState_416_; lean_object* v_snapshotTasks_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_snd_386_);
lean_dec(v_fst_385_);
lean_dec_ref(v_msg_372_);
lean_dec_ref(v_tag_368_);
lean_dec(v_cls_366_);
v___x_407_ = lean_st_ref_take(v___y_375_);
v_traceState_408_ = lean_ctor_get(v___x_407_, 4);
v_env_409_ = lean_ctor_get(v___x_407_, 0);
v_nextMacroScope_410_ = lean_ctor_get(v___x_407_, 1);
v_ngen_411_ = lean_ctor_get(v___x_407_, 2);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_407_, 3);
v_cache_413_ = lean_ctor_get(v___x_407_, 5);
v_recordedDeps_414_ = lean_ctor_get(v___x_407_, 6);
v_messages_415_ = lean_ctor_get(v___x_407_, 7);
v_infoState_416_ = lean_ctor_get(v___x_407_, 8);
v_snapshotTasks_417_ = lean_ctor_get(v___x_407_, 9);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_436_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_436_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snapshotTasks_417_);
lean_inc(v_infoState_416_);
lean_inc(v_messages_415_);
lean_inc(v_recordedDeps_414_);
lean_inc(v_cache_413_);
lean_inc(v_traceState_408_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_ngen_411_);
lean_inc(v_nextMacroScope_410_);
lean_inc(v_env_409_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_436_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint64_t v_tid_421_; lean_object* v_traces_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_435_; 
v_tid_421_ = lean_ctor_get_uint64(v_traceState_408_, sizeof(void*)*1);
v_traces_422_ = lean_ctor_get(v_traceState_408_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_traceState_408_);
if (v_isSharedCheck_435_ == 0)
{
v___x_424_ = v_traceState_408_;
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_traces_422_);
lean_dec(v_traceState_408_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_371_, v_traces_422_);
lean_dec_ref(v_traces_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_426_);
lean_ctor_set_uint64(v_reuseFailAlloc_434_, sizeof(void*)*1, v_tid_421_);
v___x_428_ = v_reuseFailAlloc_434_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 4, v___x_428_);
v___x_430_ = v___x_419_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_env_409_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_nextMacroScope_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_ngen_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_cache_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_recordedDeps_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_messages_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_infoState_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_snapshotTasks_417_);
v___x_430_ = v_reuseFailAlloc_433_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_st_ref_put(v___y_375_, v___x_430_);
v___x_432_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_377_);
return v___x_432_;
}
}
}
}
}
else
{
goto v___jp_400_;
}
}
else
{
goto v___jp_400_;
}
}
v___jp_437_:
{
double v___x_439_; double v___x_440_; double v___x_441_; uint8_t v___x_442_; 
v___x_439_ = lean_unbox_float(v_snd_386_);
v___x_440_ = lean_unbox_float(v_fst_385_);
v___x_441_ = lean_float_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_float_decLt(v___y_438_, v___x_441_);
v___y_406_ = v___x_442_;
goto v___jp_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_453_, lean_object* v_collapsed_454_, lean_object* v_tag_455_, lean_object* v_opts_456_, lean_object* v_clsEnabled_457_, lean_object* v_oldTraces_458_, lean_object* v_msg_459_, lean_object* v_resStartStop_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
uint8_t v_collapsed_boxed_464_; uint8_t v_clsEnabled_boxed_465_; lean_object* v_res_466_; 
v_collapsed_boxed_464_ = lean_unbox(v_collapsed_454_);
v_clsEnabled_boxed_465_ = lean_unbox(v_clsEnabled_457_);
v_res_466_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_453_, v_collapsed_boxed_464_, v_tag_455_, v_opts_456_, v_clsEnabled_boxed_465_, v_oldTraces_458_, v_msg_459_, v_resStartStop_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec_ref(v_opts_456_);
return v_res_466_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1000000000u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_482_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_483_ = l_Lean_Name_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_488_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_489_ = l_Lean_Name_append(v___x_488_, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_511_, lean_object* v_s_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
uint8_t v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v_a_527_; uint8_t v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v_a_547_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v_a_560_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; uint8_t v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v_a_587_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v_a_610_; uint8_t v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v_a_623_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; uint8_t v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; uint8_t v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v_element_717_; lean_object* v_children_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_888_; 
v_element_717_ = lean_ctor_get(v_s_512_, 0);
v_children_718_ = lean_ctor_get(v_s_512_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_s_512_);
if (v_isSharedCheck_888_ == 0)
{
v___x_720_ = v_s_512_;
v_isShared_721_ = v_isSharedCheck_888_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_children_718_);
lean_inc(v_element_717_);
lean_dec(v_s_512_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_888_;
goto v_resetjp_719_;
}
v___jp_516_:
{
lean_object* v___x_528_; double v___x_529_; double v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_528_ = lean_io_get_num_heartbeats();
v___x_529_ = lean_float_of_nat(v___y_526_);
v___x_530_ = lean_float_of_nat(v___x_528_);
v___x_531_ = lean_box_float(v___x_529_);
v___x_532_ = lean_box_float(v___x_530_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_527_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_525_);
v___x_535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_525_, v___y_521_, v___y_518_, v___y_523_, v___y_517_, v___y_520_, v___y_524_, v___x_534_, v___y_519_, v___y_522_);
return v___x_535_;
}
v___jp_536_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_a_547_);
v___y_517_ = v___y_537_;
v___y_518_ = v___y_538_;
v___y_519_ = v___y_539_;
v___y_520_ = v___y_540_;
v___y_521_ = v___y_541_;
v___y_522_ = v___y_543_;
v___y_523_ = v___y_542_;
v___y_524_ = v___y_544_;
v___y_525_ = v___y_546_;
v___y_526_ = v___y_545_;
v_a_527_ = v___x_548_;
goto v___jp_516_;
}
v___jp_549_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_a_560_);
v___y_517_ = v___y_550_;
v___y_518_ = v___y_551_;
v___y_519_ = v___y_552_;
v___y_520_ = v___y_553_;
v___y_521_ = v___y_554_;
v___y_522_ = v___y_556_;
v___y_523_ = v___y_555_;
v___y_524_ = v___y_557_;
v___y_525_ = v___y_559_;
v___y_526_ = v___y_558_;
v_a_527_ = v___x_561_;
goto v___jp_516_;
}
v___jp_562_:
{
if (lean_obj_tag(v___y_573_) == 0)
{
lean_object* v_a_574_; 
v_a_574_ = lean_ctor_get(v___y_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___y_573_, 1);
v___y_537_ = v___y_563_;
v___y_538_ = v___y_564_;
v___y_539_ = v___y_565_;
v___y_540_ = v___y_566_;
v___y_541_ = v___y_567_;
v___y_542_ = v___y_569_;
v___y_543_ = v___y_568_;
v___y_544_ = v___y_570_;
v___y_545_ = v___y_572_;
v___y_546_ = v___y_571_;
v_a_547_ = v_a_574_;
goto v___jp_536_;
}
else
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___y_573_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___y_573_, 1);
v___y_550_ = v___y_563_;
v___y_551_ = v___y_564_;
v___y_552_ = v___y_565_;
v___y_553_ = v___y_566_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_569_;
v___y_556_ = v___y_568_;
v___y_557_ = v___y_570_;
v___y_558_ = v___y_572_;
v___y_559_ = v___y_571_;
v_a_560_ = v_a_575_;
goto v___jp_549_;
}
}
v___jp_576_:
{
lean_object* v___x_588_; double v___x_589_; double v___x_590_; double v___x_591_; double v___x_592_; double v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_588_ = lean_io_mono_nanos_now();
v___x_589_ = lean_float_of_nat(v___y_582_);
v___x_590_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_591_ = lean_float_div(v___x_589_, v___x_590_);
v___x_592_ = lean_float_of_nat(v___x_588_);
v___x_593_ = lean_float_div(v___x_592_, v___x_590_);
v___x_594_ = lean_box_float(v___x_591_);
v___x_595_ = lean_box_float(v___x_593_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_a_587_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_586_);
v___x_598_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_586_, v___y_581_, v___y_578_, v___y_584_, v___y_577_, v___y_580_, v___y_585_, v___x_597_, v___y_579_, v___y_583_);
return v___x_598_;
}
v___jp_599_:
{
lean_object* v___x_611_; 
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_a_610_);
v___y_577_ = v___y_600_;
v___y_578_ = v___y_601_;
v___y_579_ = v___y_602_;
v___y_580_ = v___y_603_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_605_;
v___y_583_ = v___y_607_;
v___y_584_ = v___y_606_;
v___y_585_ = v___y_608_;
v___y_586_ = v___y_609_;
v_a_587_ = v___x_611_;
goto v___jp_576_;
}
v___jp_612_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_a_623_);
v___y_577_ = v___y_613_;
v___y_578_ = v___y_614_;
v___y_579_ = v___y_615_;
v___y_580_ = v___y_616_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_618_;
v___y_583_ = v___y_620_;
v___y_584_ = v___y_619_;
v___y_585_ = v___y_621_;
v___y_586_ = v___y_622_;
v_a_587_ = v___x_624_;
goto v___jp_576_;
}
v___jp_625_:
{
if (lean_obj_tag(v___y_636_) == 0)
{
lean_object* v_a_637_; 
v_a_637_ = lean_ctor_get(v___y_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___y_636_, 1);
v___y_600_ = v___y_626_;
v___y_601_ = v___y_627_;
v___y_602_ = v___y_628_;
v___y_603_ = v___y_629_;
v___y_604_ = v___y_630_;
v___y_605_ = v___y_631_;
v___y_606_ = v___y_633_;
v___y_607_ = v___y_632_;
v___y_608_ = v___y_634_;
v___y_609_ = v___y_635_;
v_a_610_ = v_a_637_;
goto v___jp_599_;
}
else
{
lean_object* v_a_638_; 
v_a_638_ = lean_ctor_get(v___y_636_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___y_636_, 1);
v___y_613_ = v___y_626_;
v___y_614_ = v___y_627_;
v___y_615_ = v___y_628_;
v___y_616_ = v___y_629_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_631_;
v___y_619_ = v___y_633_;
v___y_620_ = v___y_632_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_635_;
v_a_623_ = v_a_638_;
goto v___jp_612_;
}
}
v___jp_639_:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_649_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_656_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_650_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_io_mono_nanos_now();
v___x_658_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_645_, v___y_646_, v___y_649_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec_ref_known(v___x_658_, 1);
if (lean_obj_tag(v___y_641_) == 1)
{
lean_object* v_val_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_val_659_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v___y_641_, 1);
v___x_660_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_647_);
v___x_661_ = l_Lean_Name_mkStr2(v___y_647_, v___x_660_);
v___x_662_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_661_);
v___x_663_ = l_Lean_Name_append(v___x_662_, v___x_661_);
v___x_664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_652_, v___y_650_, v___x_663_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v___x_661_);
lean_dec(v_val_659_);
v___x_665_ = lean_box(0);
v___y_600_ = v___y_640_;
v___y_601_ = v___y_644_;
v___y_602_ = v___y_646_;
v___y_603_ = v_a_654_;
v___y_604_ = v___y_648_;
v___y_605_ = v___x_657_;
v___y_606_ = v___y_650_;
v___y_607_ = v___y_649_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_651_;
v_a_610_ = v___x_665_;
goto v___jp_599_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_Elab_InfoTree_format(v_val_659_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_MessageData_ofFormat(v_a_668_);
v___x_670_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_661_, v___x_669_, v___y_646_, v___y_649_);
v___y_626_ = v___y_640_;
v___y_627_ = v___y_644_;
v___y_628_ = v___y_646_;
v___y_629_ = v_a_654_;
v___y_630_ = v___y_648_;
v___y_631_ = v___x_657_;
v___y_632_ = v___y_649_;
v___y_633_ = v___y_650_;
v___y_634_ = v___y_642_;
v___y_635_ = v___y_651_;
v___y_636_ = v___x_670_;
goto v___jp_625_;
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_681_; 
lean_dec(v___x_661_);
v_a_671_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_681_ == 0)
{
v___x_673_ = v___x_667_;
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_667_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_io_error_to_string(v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 3);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_680_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Lean_MessageData_ofFormat(v___x_677_);
lean_inc(v___y_643_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_643_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___y_613_ = v___y_640_;
v___y_614_ = v___y_644_;
v___y_615_ = v___y_646_;
v___y_616_ = v_a_654_;
v___y_617_ = v___y_648_;
v___y_618_ = v___x_657_;
v___y_619_ = v___y_650_;
v___y_620_ = v___y_649_;
v___y_621_ = v___y_642_;
v___y_622_ = v___y_651_;
v_a_623_ = v___x_679_;
goto v___jp_612_;
}
}
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v___y_641_);
v___x_682_ = lean_box(0);
v___y_600_ = v___y_640_;
v___y_601_ = v___y_644_;
v___y_602_ = v___y_646_;
v___y_603_ = v_a_654_;
v___y_604_ = v___y_648_;
v___y_605_ = v___x_657_;
v___y_606_ = v___y_650_;
v___y_607_ = v___y_649_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_651_;
v_a_610_ = v___x_682_;
goto v___jp_599_;
}
}
else
{
lean_dec(v___y_641_);
v___y_626_ = v___y_640_;
v___y_627_ = v___y_644_;
v___y_628_ = v___y_646_;
v___y_629_ = v_a_654_;
v___y_630_ = v___y_648_;
v___y_631_ = v___x_657_;
v___y_632_ = v___y_649_;
v___y_633_ = v___y_650_;
v___y_634_ = v___y_642_;
v___y_635_ = v___y_651_;
v___y_636_ = v___x_658_;
goto v___jp_625_;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_io_get_num_heartbeats();
v___x_684_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_645_, v___y_646_, v___y_649_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v___y_641_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_val_685_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___y_641_, 1);
v___x_686_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_647_);
v___x_687_ = l_Lean_Name_mkStr2(v___y_647_, v___x_686_);
v___x_688_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_687_);
v___x_689_ = l_Lean_Name_append(v___x_688_, v___x_687_);
v___x_690_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_652_, v___y_650_, v___x_689_);
lean_dec(v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_dec(v___x_687_);
lean_dec(v_val_685_);
v___x_691_ = lean_box(0);
v___y_537_ = v___y_640_;
v___y_538_ = v___y_644_;
v___y_539_ = v___y_646_;
v___y_540_ = v_a_654_;
v___y_541_ = v___y_648_;
v___y_542_ = v___y_650_;
v___y_543_ = v___y_649_;
v___y_544_ = v___y_642_;
v___y_545_ = v___x_683_;
v___y_546_ = v___y_651_;
v_a_547_ = v___x_691_;
goto v___jp_536_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Elab_InfoTree_format(v_val_685_, v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Lean_MessageData_ofFormat(v_a_694_);
v___x_696_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_687_, v___x_695_, v___y_646_, v___y_649_);
v___y_563_ = v___y_640_;
v___y_564_ = v___y_644_;
v___y_565_ = v___y_646_;
v___y_566_ = v_a_654_;
v___y_567_ = v___y_648_;
v___y_568_ = v___y_649_;
v___y_569_ = v___y_650_;
v___y_570_ = v___y_642_;
v___y_571_ = v___y_651_;
v___y_572_ = v___x_683_;
v___y_573_ = v___x_696_;
goto v___jp_562_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
lean_dec(v___x_687_);
v_a_697_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_707_ == 0)
{
v___x_699_ = v___x_693_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_io_error_to_string(v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 3);
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l_Lean_MessageData_ofFormat(v___x_703_);
lean_inc(v___y_643_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___y_643_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___y_550_ = v___y_640_;
v___y_551_ = v___y_644_;
v___y_552_ = v___y_646_;
v___y_553_ = v_a_654_;
v___y_554_ = v___y_648_;
v___y_555_ = v___y_650_;
v___y_556_ = v___y_649_;
v___y_557_ = v___y_642_;
v___y_558_ = v___x_683_;
v___y_559_ = v___y_651_;
v_a_560_ = v___x_705_;
goto v___jp_549_;
}
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v___y_641_);
v___x_708_ = lean_box(0);
v___y_537_ = v___y_640_;
v___y_538_ = v___y_644_;
v___y_539_ = v___y_646_;
v___y_540_ = v_a_654_;
v___y_541_ = v___y_648_;
v___y_542_ = v___y_650_;
v___y_543_ = v___y_649_;
v___y_544_ = v___y_642_;
v___y_545_ = v___x_683_;
v___y_546_ = v___y_651_;
v_a_547_ = v___x_708_;
goto v___jp_536_;
}
}
else
{
lean_dec(v___y_641_);
v___y_563_ = v___y_640_;
v___y_564_ = v___y_644_;
v___y_565_ = v___y_646_;
v___y_566_ = v_a_654_;
v___y_567_ = v___y_648_;
v___y_568_ = v___y_649_;
v___y_569_ = v___y_650_;
v___y_570_ = v___y_642_;
v___y_571_ = v___y_651_;
v___y_572_ = v___x_683_;
v___y_573_ = v___x_684_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v___y_645_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
v_a_709_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_653_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_653_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v_resetjp_719_:
{
lean_object* v_desc_722_; lean_object* v_diagnostics_723_; lean_object* v_infoTree_x3f_724_; lean_object* v_desc_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___x_823_; 
v_desc_722_ = lean_ctor_get(v_element_717_, 0);
lean_inc_ref(v_desc_722_);
v_diagnostics_723_ = lean_ctor_get(v_element_717_, 1);
lean_inc_ref(v_diagnostics_723_);
v_infoTree_x3f_724_ = lean_ctor_get(v_element_717_, 2);
lean_inc(v_infoTree_x3f_724_);
lean_dec_ref(v_element_717_);
v___x_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_823_, 0, v_desc_722_);
switch(lean_obj_tag(v_range_x3f_511_))
{
case 0:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v_desc_726_ = v___x_825_;
v___y_727_ = v_a_513_;
v___y_728_ = v_a_514_;
goto v___jp_725_;
}
case 1:
{
lean_object* v_toCold_826_; lean_object* v_range_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_885_; 
v_toCold_826_ = lean_ctor_get(v_a_513_, 0);
v_range_827_ = lean_ctor_get(v_range_x3f_511_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_range_x3f_511_);
if (v_isSharedCheck_885_ == 0)
{
v___x_829_ = v_range_x3f_511_;
v_isShared_830_ = v_isSharedCheck_885_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_range_827_);
lean_dec(v_range_x3f_511_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_885_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fileMap_831_; lean_object* v_start_832_; lean_object* v_stop_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_884_; 
v_fileMap_831_ = lean_ctor_get(v_toCold_826_, 1);
v_start_832_ = lean_ctor_get(v_range_827_, 0);
v_stop_833_ = lean_ctor_get(v_range_827_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_range_827_);
if (v_isSharedCheck_884_ == 0)
{
v___x_835_ = v_range_827_;
v_isShared_836_ = v_isSharedCheck_884_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_stop_833_);
lean_inc(v_start_832_);
lean_dec(v_range_827_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_884_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v_line_838_; lean_object* v_column_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_883_; 
lean_inc_ref(v_fileMap_831_);
v___x_837_ = l_Lean_FileMap_toPosition(v_fileMap_831_, v_start_832_);
lean_dec(v_start_832_);
v_line_838_ = lean_ctor_get(v___x_837_, 0);
v_column_839_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_883_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_column_839_);
lean_inc(v_line_838_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_line_844_; lean_object* v_column_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_882_; 
lean_inc_ref(v_fileMap_831_);
v___x_843_ = l_Lean_FileMap_toPosition(v_fileMap_831_, v_stop_833_);
lean_dec(v_stop_833_);
v_line_844_ = lean_ctor_get(v___x_843_, 0);
v_column_845_ = lean_ctor_get(v___x_843_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_882_ == 0)
{
v___x_847_ = v___x_843_;
v_isShared_848_ = v_isSharedCheck_882_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_column_845_);
lean_inc(v_line_844_);
lean_dec(v___x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_882_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_850_ = l_Nat_reprFast(v_line_838_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 3);
lean_ctor_set(v___x_829_, 0, v___x_850_);
v___x_852_ = v___x_829_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_881_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 5);
lean_ctor_set(v___x_847_, 1, v___x_852_);
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_854_ = v___x_847_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_880_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 5);
lean_ctor_set(v___x_841_, 1, v___x_855_);
lean_ctor_set(v___x_841_, 0, v___x_854_);
v___x_857_ = v___x_841_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_879_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = l_Nat_reprFast(v_column_839_);
v___x_859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 5);
lean_ctor_set(v___x_835_, 1, v___x_859_);
lean_ctor_set(v___x_835_, 0, v___x_857_);
v___x_861_ = v___x_835_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_878_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_862_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Nat_reprFast(v_line_844_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_849_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_855_);
v___x_870_ = l_Nat_reprFast(v_column_845_);
v___x_871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_869_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_862_);
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_865_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_823_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v_desc_726_ = v___x_877_;
v___y_727_ = v_a_513_;
v___y_728_ = v_a_514_;
goto v___jp_725_;
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
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_823_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v_desc_726_ = v___x_887_;
v___y_727_ = v_a_513_;
v___y_728_ = v_a_514_;
goto v___jp_725_;
}
}
v___jp_725_:
{
lean_object* v_msgLog_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_821_; 
v_msgLog_729_ = lean_ctor_get(v_diagnostics_723_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_diagnostics_723_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_diagnostics_723_, 1);
lean_dec(v_unused_822_);
v___x_731_ = v_diagnostics_723_;
v_isShared_732_ = v_isSharedCheck_821_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_msgLog_729_);
lean_dec(v_diagnostics_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_821_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = l_Lean_MessageLog_toList(v_msgLog_729_);
lean_dec_ref(v_msgLog_729_);
v___x_734_ = lean_box(0);
v___x_735_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_733_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_toCold_736_; lean_object* v_options_737_; lean_object* v_a_738_; lean_object* v_ref_739_; lean_object* v_inheritedTraceOptions_740_; uint8_t v_hasTrace_741_; lean_object* v___x_742_; 
v_toCold_736_ = lean_ctor_get(v___y_727_, 0);
v_options_737_ = lean_ctor_get(v_toCold_736_, 2);
v_a_738_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_735_, 1);
v_ref_739_ = lean_ctor_get(v___y_727_, 2);
v_inheritedTraceOptions_740_ = lean_ctor_get(v_toCold_736_, 11);
v_hasTrace_741_ = lean_ctor_get_uint8(v_options_737_, sizeof(void*)*1);
v___x_742_ = lean_array_to_list(v_children_718_);
if (v_hasTrace_741_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_a_738_);
lean_del_object(v___x_731_);
lean_dec(v_desc_726_);
lean_del_object(v___x_720_);
v___x_743_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_742_, v___y_727_, v___y_728_);
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
if (lean_obj_tag(v_infoTree_x3f_724_) == 1)
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec_ref_known(v_infoTree_x3f_724_, 1);
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
lean_dec(v_infoTree_x3f_724_);
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
lean_dec(v_infoTree_x3f_724_);
return v___x_743_;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_758_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_759_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_758_, v_a_738_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 5);
lean_ctor_set(v___x_731_, 1, v___x_759_);
lean_ctor_set(v___x_731_, 0, v_desc_726_);
v___x_761_ = v___x_731_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_desc_726_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_812_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___f_762_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_762_, 0, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_764_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_765_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_740_, v_options_737_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = l_Lean_trace_profiler;
v___x_768_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_737_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___f_762_);
v___x_769_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_742_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_810_; 
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_811_);
v___x_771_ = v___x_769_;
v_isShared_772_ = v_isSharedCheck_810_;
goto v_resetjp_770_;
}
else
{
lean_dec(v___x_769_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_810_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
if (lean_obj_tag(v_infoTree_x3f_724_) == 1)
{
lean_object* v_val_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_805_; 
v_val_773_ = lean_ctor_get(v_infoTree_x3f_724_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_infoTree_x3f_724_);
if (v_isSharedCheck_805_ == 0)
{
v___x_775_ = v_infoTree_x3f_724_;
v_isShared_776_ = v_isSharedCheck_805_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_val_773_);
lean_dec(v_infoTree_x3f_724_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_805_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_778_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_740_, v_options_737_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_del_object(v___x_775_);
lean_dec(v_val_773_);
lean_del_object(v___x_720_);
v___x_780_ = lean_box(0);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_780_);
v___x_782_ = v___x_771_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_771_);
v___x_784_ = lean_box(0);
v___x_785_ = l_Lean_Elab_InfoTree_format(v_val_773_, v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_775_);
lean_del_object(v___x_720_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_MessageData_ofFormat(v_a_786_);
v___x_788_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_777_, v___x_787_, v___y_727_, v___y_728_);
return v___x_788_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_804_; 
v_a_789_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_791_ = v___x_785_;
v_isShared_792_ = v_isSharedCheck_804_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_785_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_804_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_io_error_to_string(v_a_789_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 3);
lean_ctor_set(v___x_775_, 0, v___x_793_);
v___x_795_ = v___x_775_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_803_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_MessageData_ofFormat(v___x_795_);
lean_inc(v_ref_739_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_796_);
lean_ctor_set(v___x_720_, 0, v_ref_739_);
v___x_798_ = v___x_720_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_ref_739_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_798_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
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
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_infoTree_x3f_724_);
lean_del_object(v___x_720_);
v___x_806_ = lean_box(0);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_806_);
v___x_808_ = v___x_771_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_724_);
lean_del_object(v___x_720_);
return v___x_769_;
}
}
else
{
lean_del_object(v___x_720_);
v___y_640_ = v___x_766_;
v___y_641_ = v_infoTree_x3f_724_;
v___y_642_ = v___f_762_;
v___y_643_ = v_ref_739_;
v___y_644_ = v___x_764_;
v___y_645_ = v___x_742_;
v___y_646_ = v___y_727_;
v___y_647_ = v___x_757_;
v___y_648_ = v_hasTrace_741_;
v___y_649_ = v___y_728_;
v___y_650_ = v_options_737_;
v___y_651_ = v___x_763_;
v___y_652_ = v_inheritedTraceOptions_740_;
goto v___jp_639_;
}
}
else
{
lean_del_object(v___x_720_);
v___y_640_ = v___x_766_;
v___y_641_ = v_infoTree_x3f_724_;
v___y_642_ = v___f_762_;
v___y_643_ = v_ref_739_;
v___y_644_ = v___x_764_;
v___y_645_ = v___x_742_;
v___y_646_ = v___y_727_;
v___y_647_ = v___x_757_;
v___y_648_ = v_hasTrace_741_;
v___y_649_ = v___y_728_;
v___y_650_ = v_options_737_;
v___y_651_ = v___x_763_;
v___y_652_ = v_inheritedTraceOptions_740_;
goto v___jp_639_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_del_object(v___x_731_);
lean_dec(v_desc_726_);
lean_dec(v_infoTree_x3f_724_);
lean_del_object(v___x_720_);
lean_dec_ref(v_children_718_);
v_a_813_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_735_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_735_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
if (lean_obj_tag(v_as_889_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v_reportingRange_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_head_895_ = lean_ctor_get(v_as_889_, 0);
lean_inc(v_head_895_);
v_tail_896_ = lean_ctor_get(v_as_889_, 1);
lean_inc(v_tail_896_);
lean_dec_ref_known(v_as_889_, 2);
v_reportingRange_897_ = lean_ctor_get(v_head_895_, 1);
lean_inc(v_reportingRange_897_);
v___x_898_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_895_);
v___x_899_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_897_, v___x_898_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_dec_ref_known(v___x_899_, 1);
v_as_889_ = v_tail_896_;
goto _start;
}
else
{
lean_dec(v_tail_896_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_906_, lean_object* v_s_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_906_, v_s_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_912_, v_x_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_918_, v_x_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_924_, lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_930_, v_x_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(2);
v___x_941_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_940_, v_s_936_, v_a_937_, v_a_938_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Language_SnapshotTree_trace(v_s_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_946_;
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

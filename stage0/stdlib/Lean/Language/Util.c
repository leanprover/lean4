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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((size_t)5ULL);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_unsigned_to_nat(32u);
v___x_7_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_8_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__0);
v___x_9_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_5_);
lean_ctor_set(v___x_9_, 3, v___x_5_);
lean_ctor_set_usize(v___x_9_, 4, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(lean_object* v___y_10_){
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
v___x_32_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg___boxed(lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___y_44_);
lean_dec(v___y_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___y_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_opts_55_, lean_object* v_opt_56_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3___boxed(lean_object* v_opts_65_, lean_object* v_opt_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v_opts_65_, v_opt_66_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_84_ = lean_ctor_get(v_x_82_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v_x_82_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v_x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_a_92_ = lean_ctor_get(v_x_82_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v_x_82_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v_x_82_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 0);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg___boxed(lean_object* v_x_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(v_x_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8(lean_object* v_opts_103_, lean_object* v_opt_104_){
_start:
{
lean_object* v_name_105_; lean_object* v_defValue_106_; lean_object* v_map_107_; lean_object* v___x_108_; 
v_name_105_ = lean_ctor_get(v_opt_104_, 0);
v_defValue_106_ = lean_ctor_get(v_opt_104_, 1);
v_map_107_ = lean_ctor_get(v_opts_103_, 0);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_107_, v_name_105_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_inc(v_defValue_106_);
return v_defValue_106_;
}
else
{
lean_object* v_val_109_; 
v_val_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_108_, 1);
if (lean_obj_tag(v_val_109_) == 3)
{
lean_object* v_v_110_; 
v_v_110_ = lean_ctor_get(v_val_109_, 0);
lean_inc(v_v_110_);
lean_dec_ref_known(v_val_109_, 1);
return v_v_110_;
}
else
{
lean_dec(v_val_109_);
lean_inc(v_defValue_106_);
return v_defValue_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8___boxed(lean_object* v_opts_111_, lean_object* v_opt_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8(v_opts_111_, v_opt_112_);
lean_dec_ref(v_opt_112_);
lean_dec_ref(v_opts_111_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7(lean_object* v_e_114_){
_start:
{
if (lean_obj_tag(v_e_114_) == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7___boxed(lean_object* v_e_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7(v_e_117_);
lean_dec_ref(v_e_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__0);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
lean_ctor_set(v___x_125_, 3, v___x_124_);
lean_ctor_set(v___x_125_, 4, v___x_123_);
lean_ctor_set(v___x_125_, 5, v___x_123_);
lean_ctor_set(v___x_125_, 6, v___x_123_);
lean_ctor_set(v___x_125_, 7, v___x_123_);
lean_ctor_set(v___x_125_, 8, v___x_123_);
lean_ctor_set(v___x_125_, 9, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(32u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4(void){
_start:
{
size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = ((size_t)5ULL);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_unsigned_to_nat(32u);
v___x_132_ = lean_mk_empty_array_with_capacity(v___x_131_);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__3);
v___x_134_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_130_);
lean_ctor_set(v___x_134_, 3, v___x_130_);
lean_ctor_set_usize(v___x_134_, 4, v___x_129_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_box(1);
v___x_136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__4);
v___x_137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__1);
v___x_138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_135_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_env_144_; lean_object* v_options_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_143_ = lean_st_ref_get(v___y_141_);
v_env_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_ref(v_env_144_);
lean_dec(v___x_143_);
v_options_145_ = lean_ctor_get(v___y_140_, 2);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__2);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___closed__5);
lean_inc_ref(v_options_145_);
v___x_148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_148_, 0, v_env_144_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
lean_ctor_set(v___x_148_, 3, v_options_145_);
v___x_149_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_msgData_139_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_msgData_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6(size_t v_sz_156_, size_t v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_157_, v_sz_156_);
if (v___x_159_ == 0)
{
return v_bs_158_;
}
else
{
lean_object* v_v_160_; lean_object* v_msg_161_; lean_object* v___x_162_; lean_object* v_bs_x27_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v_v_160_ = lean_array_uget_borrowed(v_bs_158_, v_i_157_);
v_msg_161_ = lean_ctor_get(v_v_160_, 1);
lean_inc_ref(v_msg_161_);
v___x_162_ = lean_unsigned_to_nat(0u);
v_bs_x27_163_ = lean_array_uset(v_bs_158_, v_i_157_, v___x_162_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_add(v_i_157_, v___x_164_);
v___x_166_ = lean_array_uset(v_bs_x27_163_, v_i_157_, v_msg_161_);
v_i_157_ = v___x_165_;
v_bs_158_ = v___x_166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_168_, lean_object* v_i_169_, lean_object* v_bs_170_){
_start:
{
size_t v_sz_boxed_171_; size_t v_i_boxed_172_; lean_object* v_res_173_; 
v_sz_boxed_171_ = lean_unbox_usize(v_sz_168_);
lean_dec(v_sz_168_);
v_i_boxed_172_ = lean_unbox_usize(v_i_169_);
lean_dec(v_i_169_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6(v_sz_boxed_171_, v_i_boxed_172_, v_bs_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(lean_object* v_oldTraces_174_, lean_object* v_data_175_, lean_object* v_ref_176_, lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_fileName_181_; lean_object* v_fileMap_182_; lean_object* v_options_183_; lean_object* v_currRecDepth_184_; lean_object* v_maxRecDepth_185_; lean_object* v_ref_186_; lean_object* v_currNamespace_187_; lean_object* v_openDecls_188_; lean_object* v_initHeartbeats_189_; lean_object* v_maxHeartbeats_190_; lean_object* v_quotContext_191_; lean_object* v_currMacroScope_192_; uint8_t v_diag_193_; lean_object* v_cancelTk_x3f_194_; uint8_t v_suppressElabErrors_195_; lean_object* v_inheritedTraceOptions_196_; lean_object* v___x_197_; lean_object* v_traceState_198_; lean_object* v_traces_199_; lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v___x_202_; size_t v_sz_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v_msg_206_; lean_object* v___x_207_; lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_245_; 
v_fileName_181_ = lean_ctor_get(v___y_178_, 0);
v_fileMap_182_ = lean_ctor_get(v___y_178_, 1);
v_options_183_ = lean_ctor_get(v___y_178_, 2);
v_currRecDepth_184_ = lean_ctor_get(v___y_178_, 3);
v_maxRecDepth_185_ = lean_ctor_get(v___y_178_, 4);
v_ref_186_ = lean_ctor_get(v___y_178_, 5);
v_currNamespace_187_ = lean_ctor_get(v___y_178_, 6);
v_openDecls_188_ = lean_ctor_get(v___y_178_, 7);
v_initHeartbeats_189_ = lean_ctor_get(v___y_178_, 8);
v_maxHeartbeats_190_ = lean_ctor_get(v___y_178_, 9);
v_quotContext_191_ = lean_ctor_get(v___y_178_, 10);
v_currMacroScope_192_ = lean_ctor_get(v___y_178_, 11);
v_diag_193_ = lean_ctor_get_uint8(v___y_178_, sizeof(void*)*14);
v_cancelTk_x3f_194_ = lean_ctor_get(v___y_178_, 12);
v_suppressElabErrors_195_ = lean_ctor_get_uint8(v___y_178_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_196_ = lean_ctor_get(v___y_178_, 13);
v___x_197_ = lean_st_ref_get(v___y_179_);
v_traceState_198_ = lean_ctor_get(v___x_197_, 4);
lean_inc_ref(v_traceState_198_);
lean_dec(v___x_197_);
v_traces_199_ = lean_ctor_get(v_traceState_198_, 0);
lean_inc_ref(v_traces_199_);
lean_dec_ref(v_traceState_198_);
v_ref_200_ = l_Lean_replaceRef(v_ref_176_, v_ref_186_);
lean_inc_ref(v_inheritedTraceOptions_196_);
lean_inc(v_cancelTk_x3f_194_);
lean_inc(v_currMacroScope_192_);
lean_inc(v_quotContext_191_);
lean_inc(v_maxHeartbeats_190_);
lean_inc(v_initHeartbeats_189_);
lean_inc(v_openDecls_188_);
lean_inc(v_currNamespace_187_);
lean_inc(v_maxRecDepth_185_);
lean_inc(v_currRecDepth_184_);
lean_inc_ref(v_options_183_);
lean_inc_ref(v_fileMap_182_);
lean_inc_ref(v_fileName_181_);
v___x_201_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_201_, 0, v_fileName_181_);
lean_ctor_set(v___x_201_, 1, v_fileMap_182_);
lean_ctor_set(v___x_201_, 2, v_options_183_);
lean_ctor_set(v___x_201_, 3, v_currRecDepth_184_);
lean_ctor_set(v___x_201_, 4, v_maxRecDepth_185_);
lean_ctor_set(v___x_201_, 5, v_ref_200_);
lean_ctor_set(v___x_201_, 6, v_currNamespace_187_);
lean_ctor_set(v___x_201_, 7, v_openDecls_188_);
lean_ctor_set(v___x_201_, 8, v_initHeartbeats_189_);
lean_ctor_set(v___x_201_, 9, v_maxHeartbeats_190_);
lean_ctor_set(v___x_201_, 10, v_quotContext_191_);
lean_ctor_set(v___x_201_, 11, v_currMacroScope_192_);
lean_ctor_set(v___x_201_, 12, v_cancelTk_x3f_194_);
lean_ctor_set(v___x_201_, 13, v_inheritedTraceOptions_196_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*14, v_diag_193_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*14 + 1, v_suppressElabErrors_195_);
v___x_202_ = l_Lean_PersistentArray_toArray___redArg(v_traces_199_);
lean_dec_ref(v_traces_199_);
v_sz_203_ = lean_array_size(v___x_202_);
v___x_204_ = ((size_t)0ULL);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5_spec__6(v_sz_203_, v___x_204_, v___x_202_);
v_msg_206_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_206_, 0, v_data_175_);
lean_ctor_set(v_msg_206_, 1, v_msg_177_);
lean_ctor_set(v_msg_206_, 2, v___x_205_);
v___x_207_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_msg_206_, v___x_201_, v___y_179_);
lean_dec_ref_known(v___x_201_, 14);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_245_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_245_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_245_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v_traceState_213_; lean_object* v_env_214_; lean_object* v_nextMacroScope_215_; lean_object* v_ngen_216_; lean_object* v_auxDeclNGen_217_; lean_object* v_cache_218_; lean_object* v_messages_219_; lean_object* v_infoState_220_; lean_object* v_snapshotTasks_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_244_; 
v___x_212_ = lean_st_ref_take(v___y_179_);
v_traceState_213_ = lean_ctor_get(v___x_212_, 4);
v_env_214_ = lean_ctor_get(v___x_212_, 0);
v_nextMacroScope_215_ = lean_ctor_get(v___x_212_, 1);
v_ngen_216_ = lean_ctor_get(v___x_212_, 2);
v_auxDeclNGen_217_ = lean_ctor_get(v___x_212_, 3);
v_cache_218_ = lean_ctor_get(v___x_212_, 5);
v_messages_219_ = lean_ctor_get(v___x_212_, 6);
v_infoState_220_ = lean_ctor_get(v___x_212_, 7);
v_snapshotTasks_221_ = lean_ctor_get(v___x_212_, 8);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_244_ == 0)
{
v___x_223_ = v___x_212_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snapshotTasks_221_);
lean_inc(v_infoState_220_);
lean_inc(v_messages_219_);
lean_inc(v_cache_218_);
lean_inc(v_traceState_213_);
lean_inc(v_auxDeclNGen_217_);
lean_inc(v_ngen_216_);
lean_inc(v_nextMacroScope_215_);
lean_inc(v_env_214_);
lean_dec(v___x_212_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint64_t v_tid_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_242_; 
v_tid_225_ = lean_ctor_get_uint64(v_traceState_213_, sizeof(void*)*1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_traceState_213_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_traceState_213_, 0);
lean_dec(v_unused_243_);
v___x_227_ = v_traceState_213_;
v_isShared_228_ = v_isSharedCheck_242_;
goto v_resetjp_226_;
}
else
{
lean_dec(v_traceState_213_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_242_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_ref_176_);
lean_ctor_set(v___x_229_, 1, v_a_208_);
v___x_230_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_174_, v___x_229_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_230_);
lean_ctor_set_uint64(v_reuseFailAlloc_241_, sizeof(void*)*1, v_tid_225_);
v___x_232_ = v_reuseFailAlloc_241_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___x_232_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_env_214_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_nextMacroScope_215_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_ngen_216_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_auxDeclNGen_217_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_240_, 5, v_cache_218_);
lean_ctor_set(v_reuseFailAlloc_240_, 6, v_messages_219_);
lean_ctor_set(v_reuseFailAlloc_240_, 7, v_infoState_220_);
lean_ctor_set(v_reuseFailAlloc_240_, 8, v_snapshotTasks_221_);
v___x_234_ = v_reuseFailAlloc_240_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_235_ = lean_st_ref_set(v___y_179_, v___x_234_);
v___x_236_ = lean_box(0);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_236_);
v___x_238_ = v___x_210_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5___boxed(lean_object* v_oldTraces_246_, lean_object* v_data_247_, lean_object* v_ref_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(v_oldTraces_246_, v_data_247_, v_ref_248_, v_msg_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_253_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0(void){
_start:
{
lean_object* v___x_254_; double v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_float_of_nat(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__1));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3(void){
_start:
{
lean_object* v___x_259_; double v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1000u);
v___x_260_ = lean_float_of_nat(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(lean_object* v_cls_261_, uint8_t v_collapsed_262_, lean_object* v_tag_263_, lean_object* v_opts_264_, uint8_t v_clsEnabled_265_, lean_object* v_oldTraces_266_, lean_object* v_msg_267_, lean_object* v_resStartStop_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v_data_277_; lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___y_285_; lean_object* v_a_286_; uint8_t v___y_301_; double v___y_332_; 
v_fst_272_ = lean_ctor_get(v_resStartStop_268_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v_resStartStop_268_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v_resStartStop_268_);
v_fst_280_ = lean_ctor_get(v_snd_273_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v_snd_273_, 1);
lean_inc(v_snd_281_);
lean_dec(v_snd_273_);
v___x_282_ = l_Lean_trace_profiler;
v___x_283_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v_opts_264_, v___x_282_);
if (v___x_283_ == 0)
{
v___y_301_ = v___x_283_;
goto v___jp_300_;
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = l_Lean_trace_profiler_useHeartbeats;
v___x_338_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v_opts_264_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; double v___x_341_; double v___x_342_; double v___x_343_; 
v___x_339_ = l_Lean_trace_profiler_threshold;
v___x_340_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8(v_opts_264_, v___x_339_);
v___x_341_ = lean_float_of_nat(v___x_340_);
v___x_342_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__3);
v___x_343_ = lean_float_div(v___x_341_, v___x_342_);
v___y_332_ = v___x_343_;
goto v___jp_331_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; double v___x_346_; 
v___x_344_ = l_Lean_trace_profiler_threshold;
v___x_345_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__8(v_opts_264_, v___x_344_);
v___x_346_ = lean_float_of_nat(v___x_345_);
v___y_332_ = v___x_346_;
goto v___jp_331_;
}
}
v___jp_274_:
{
lean_object* v___x_278_; 
lean_inc(v___y_275_);
v___x_278_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__5(v_oldTraces_266_, v_data_277_, v___y_275_, v___y_276_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(v_fst_272_);
return v___x_279_;
}
else
{
lean_dec(v_fst_272_);
return v___x_278_;
}
}
v___jp_284_:
{
uint8_t v_result_287_; lean_object* v___x_288_; lean_object* v___x_289_; double v___x_290_; lean_object* v_data_291_; 
v_result_287_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__7(v_fst_272_);
v___x_288_ = lean_box(v_result_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0);
lean_inc_ref(v_tag_263_);
lean_inc_ref(v___x_289_);
lean_inc(v_cls_261_);
v_data_291_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_291_, 0, v_cls_261_);
lean_ctor_set(v_data_291_, 1, v___x_289_);
lean_ctor_set(v_data_291_, 2, v_tag_263_);
lean_ctor_set_float(v_data_291_, sizeof(void*)*3, v___x_290_);
lean_ctor_set_float(v_data_291_, sizeof(void*)*3 + 8, v___x_290_);
lean_ctor_set_uint8(v_data_291_, sizeof(void*)*3 + 16, v_collapsed_262_);
if (v___x_283_ == 0)
{
lean_dec_ref_known(v___x_289_, 1);
lean_dec(v_snd_281_);
lean_dec(v_fst_280_);
lean_dec_ref(v_tag_263_);
lean_dec(v_cls_261_);
v___y_275_ = v___y_285_;
v___y_276_ = v_a_286_;
v_data_277_ = v_data_291_;
goto v___jp_274_;
}
else
{
lean_object* v_data_292_; double v___x_293_; double v___x_294_; 
lean_dec_ref_known(v_data_291_, 3);
v_data_292_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_292_, 0, v_cls_261_);
lean_ctor_set(v_data_292_, 1, v___x_289_);
lean_ctor_set(v_data_292_, 2, v_tag_263_);
v___x_293_ = lean_unbox_float(v_fst_280_);
lean_dec(v_fst_280_);
lean_ctor_set_float(v_data_292_, sizeof(void*)*3, v___x_293_);
v___x_294_ = lean_unbox_float(v_snd_281_);
lean_dec(v_snd_281_);
lean_ctor_set_float(v_data_292_, sizeof(void*)*3 + 8, v___x_294_);
lean_ctor_set_uint8(v_data_292_, sizeof(void*)*3 + 16, v_collapsed_262_);
v___y_275_ = v___y_285_;
v___y_276_ = v_a_286_;
v_data_277_ = v_data_292_;
goto v___jp_274_;
}
}
v___jp_295_:
{
lean_object* v_ref_296_; lean_object* v___x_297_; 
v_ref_296_ = lean_ctor_get(v___y_269_, 5);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
lean_inc(v_fst_272_);
v___x_297_ = lean_apply_4(v_msg_267_, v_fst_272_, v___y_269_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___y_285_ = v_ref_296_;
v_a_286_ = v_a_298_;
goto v___jp_284_;
}
else
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__2);
v___y_285_ = v_ref_296_;
v_a_286_ = v___x_299_;
goto v___jp_284_;
}
}
v___jp_300_:
{
if (v_clsEnabled_265_ == 0)
{
if (v___y_301_ == 0)
{
lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_snd_281_);
lean_dec(v_fst_280_);
lean_dec_ref(v_msg_267_);
lean_dec_ref(v_tag_263_);
lean_dec(v_cls_261_);
v___x_302_ = lean_st_ref_take(v___y_270_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
v_env_304_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_305_ = lean_ctor_get(v___x_302_, 1);
v_ngen_306_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_307_ = lean_ctor_get(v___x_302_, 3);
v_cache_308_ = lean_ctor_get(v___x_302_, 5);
v_messages_309_ = lean_ctor_get(v___x_302_, 6);
v_infoState_310_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_311_ = lean_ctor_get(v___x_302_, 8);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_330_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snapshotTasks_311_);
lean_inc(v_infoState_310_);
lean_inc(v_messages_309_);
lean_inc(v_cache_308_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_307_);
lean_inc(v_ngen_306_);
lean_inc(v_nextMacroScope_305_);
lean_inc(v_env_304_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v_traces_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_329_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_traces_316_ = lean_ctor_get(v_traceState_303_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_329_ == 0)
{
v___x_318_ = v_traceState_303_;
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_traces_316_);
lean_dec(v_traceState_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_266_, v_traces_316_);
lean_dec_ref(v_traces_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_320_);
lean_ctor_set_uint64(v_reuseFailAlloc_328_, sizeof(void*)*1, v_tid_315_);
v___x_322_ = v_reuseFailAlloc_328_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_322_);
v___x_324_ = v___x_313_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_snapshotTasks_311_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_st_ref_set(v___y_270_, v___x_324_);
v___x_326_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(v_fst_272_);
return v___x_326_;
}
}
}
}
}
else
{
goto v___jp_295_;
}
}
else
{
goto v___jp_295_;
}
}
v___jp_331_:
{
double v___x_333_; double v___x_334_; double v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_unbox_float(v_snd_281_);
v___x_334_ = lean_unbox_float(v_fst_280_);
v___x_335_ = lean_float_sub(v___x_333_, v___x_334_);
v___x_336_ = lean_float_decLt(v___y_332_, v___x_335_);
v___y_301_ = v___x_336_;
goto v___jp_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___boxed(lean_object* v_cls_347_, lean_object* v_collapsed_348_, lean_object* v_tag_349_, lean_object* v_opts_350_, lean_object* v_clsEnabled_351_, lean_object* v_oldTraces_352_, lean_object* v_msg_353_, lean_object* v_resStartStop_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
uint8_t v_collapsed_boxed_358_; uint8_t v_clsEnabled_boxed_359_; lean_object* v_res_360_; 
v_collapsed_boxed_358_ = lean_unbox(v_collapsed_348_);
v_clsEnabled_boxed_359_ = lean_unbox(v_clsEnabled_351_);
v_res_360_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v_cls_347_, v_collapsed_boxed_358_, v_tag_349_, v_opts_350_, v_clsEnabled_boxed_359_, v_oldTraces_352_, v_msg_353_, v_resStartStop_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec_ref(v_opts_350_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_415_; 
v_ref_369_ = lean_ctor_get(v___y_366_, 5);
v___x_370_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_msg_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_415_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_415_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_415_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v_traceState_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_cache_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_414_; 
v___x_375_ = lean_st_ref_take(v___y_367_);
v_traceState_376_ = lean_ctor_get(v___x_375_, 4);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
v_cache_381_ = lean_ctor_get(v___x_375_, 5);
v_messages_382_ = lean_ctor_get(v___x_375_, 6);
v_infoState_383_ = lean_ctor_get(v___x_375_, 7);
v_snapshotTasks_384_ = lean_ctor_get(v___x_375_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_414_ == 0)
{
v___x_386_ = v___x_375_;
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_cache_381_);
lean_inc(v_traceState_376_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint64_t v_tid_388_; lean_object* v_traces_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_413_; 
v_tid_388_ = lean_ctor_get_uint64(v_traceState_376_, sizeof(void*)*1);
v_traces_389_ = lean_ctor_get(v_traceState_376_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_traceState_376_);
if (v_isSharedCheck_413_ == 0)
{
v___x_391_ = v_traceState_376_;
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_traces_389_);
lean_dec(v_traceState_376_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; double v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___closed__0);
v___x_395_ = 0;
v___x_396_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_397_, 0, v_cls_364_);
lean_ctor_set(v___x_397_, 1, v___x_393_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3, v___x_394_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3 + 8, v___x_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 16, v___x_395_);
v___x_398_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1));
v___x_399_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v_a_371_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_inc(v_ref_369_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_369_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_PersistentArray_push___redArg(v_traces_389_, v___x_400_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_401_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_401_);
lean_ctor_set_uint64(v_reuseFailAlloc_412_, sizeof(void*)*1, v_tid_388_);
v___x_403_ = v_reuseFailAlloc_412_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v___x_403_);
v___x_405_ = v___x_386_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_env_377_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_382_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_384_);
v___x_405_ = v_reuseFailAlloc_411_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_st_ref_set(v___y_367_, v___x_405_);
v___x_407_ = lean_box(0);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_407_);
v___x_409_ = v___x_373_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_416_, v_msg_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1_spec__1(lean_object* v_pre_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_dec(v_pre_422_);
return v_x_423_;
}
else
{
lean_object* v_head_425_; lean_object* v_tail_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_436_; 
v_head_425_ = lean_ctor_get(v_x_424_, 0);
v_tail_426_ = lean_ctor_get(v_x_424_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_436_ == 0)
{
v___x_428_ = v_x_424_;
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_tail_426_);
lean_inc(v_head_425_);
lean_dec(v_x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
lean_inc(v_pre_422_);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 5);
lean_ctor_set(v___x_428_, 1, v_pre_422_);
lean_ctor_set(v___x_428_, 0, v_x_423_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_x_423_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_pre_422_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_432_, 0, v_head_425_);
v___x_433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v_x_423_ = v___x_433_;
v_x_424_ = v_tail_426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_pre_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v___x_439_; 
lean_dec(v_pre_437_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v_head_440_; lean_object* v_tail_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_450_; 
v_head_440_ = lean_ctor_get(v_x_438_, 0);
v_tail_441_ = lean_ctor_get(v_x_438_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_450_ == 0)
{
v___x_443_ = v_x_438_;
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_tail_441_);
lean_inc(v_head_440_);
lean_dec(v_x_438_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_445_, 0, v_head_440_);
lean_inc(v_pre_437_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 5);
lean_ctor_set(v___x_443_, 1, v___x_445_);
lean_ctor_set(v___x_443_, 0, v_pre_437_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_pre_437_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_449_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; 
v___x_448_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1_spec__1(v_pre_437_, v___x_447_, v_tail_441_);
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = l_List_reverse___redArg(v_x_452_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_head_456_; lean_object* v_tail_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v_head_456_ = lean_ctor_get(v_x_451_, 0);
v_tail_457_ = lean_ctor_get(v_x_451_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_467_ == 0)
{
v___x_459_ = v_x_451_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_tail_457_);
lean_inc(v_head_456_);
lean_dec(v_x_451_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = 0;
v___x_462_ = l_Lean_Message_toString(v_head_456_, v___x_461_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_x_452_);
lean_ctor_set(v___x_459_, 0, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_x_452_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v_x_451_ = v_tail_457_;
v_x_452_ = v___x_464_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_468_, v_x_469_);
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
lean_object* v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; lean_object* v_a_538_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_557_; lean_object* v_a_558_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; lean_object* v___y_573_; lean_object* v___y_574_; uint8_t v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v_a_583_; lean_object* v___y_586_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; uint8_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v_a_610_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v_a_633_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v_a_658_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint8_t v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint8_t v___y_680_; uint8_t v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v_a_765_; lean_object* v_element_807_; lean_object* v_children_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_964_; 
v_element_807_ = lean_ctor_get(v_s_517_, 0);
v_children_808_ = lean_ctor_get(v_s_517_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_s_517_);
if (v_isSharedCheck_964_ == 0)
{
v___x_810_ = v_s_517_;
v_isShared_811_ = v_isSharedCheck_964_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_children_808_);
lean_inc(v_element_807_);
lean_dec(v_s_517_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_964_;
goto v_resetjp_809_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
v___jp_527_:
{
lean_object* v___x_539_; double v___x_540_; double v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_539_ = lean_io_get_num_heartbeats();
v___x_540_ = lean_float_of_nat(v___y_533_);
v___x_541_ = lean_float_of_nat(v___x_539_);
v___x_542_ = lean_box_float(v___x_540_);
v___x_543_ = lean_box_float(v___x_541_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_a_538_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
v___x_546_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_531_, v___y_537_, v___y_532_, v___y_536_, v___y_530_, v___y_528_, v___y_535_, v___x_545_, v___y_534_, v___y_529_);
return v___x_546_;
}
v___jp_547_:
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_a_558_);
v___y_528_ = v___y_548_;
v___y_529_ = v___y_551_;
v___y_530_ = v___y_550_;
v___y_531_ = v___y_549_;
v___y_532_ = v___y_552_;
v___y_533_ = v___y_553_;
v___y_534_ = v___y_554_;
v___y_535_ = v___y_555_;
v___y_536_ = v___y_556_;
v___y_537_ = v___y_557_;
v_a_538_ = v___x_559_;
goto v___jp_527_;
}
v___jp_560_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
v___y_548_ = v___y_561_;
v___y_549_ = v___y_564_;
v___y_550_ = v___y_563_;
v___y_551_ = v___y_562_;
v___y_552_ = v___y_565_;
v___y_553_ = v___y_566_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_568_;
v___y_556_ = v___y_569_;
v___y_557_ = v___y_570_;
v_a_558_ = v___x_571_;
goto v___jp_547_;
}
v___jp_572_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_a_583_);
v___y_528_ = v___y_573_;
v___y_529_ = v___y_576_;
v___y_530_ = v___y_575_;
v___y_531_ = v___y_574_;
v___y_532_ = v___y_577_;
v___y_533_ = v___y_578_;
v___y_534_ = v___y_579_;
v___y_535_ = v___y_580_;
v___y_536_ = v___y_581_;
v___y_537_ = v___y_582_;
v_a_538_ = v___x_584_;
goto v___jp_527_;
}
v___jp_585_:
{
if (lean_obj_tag(v___y_596_) == 0)
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___y_596_, 1);
v___y_548_ = v___y_586_;
v___y_549_ = v___y_589_;
v___y_550_ = v___y_588_;
v___y_551_ = v___y_587_;
v___y_552_ = v___y_590_;
v___y_553_ = v___y_591_;
v___y_554_ = v___y_592_;
v___y_555_ = v___y_593_;
v___y_556_ = v___y_594_;
v___y_557_ = v___y_595_;
v_a_558_ = v_a_597_;
goto v___jp_547_;
}
else
{
lean_object* v_a_598_; 
v_a_598_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___y_596_, 1);
v___y_573_ = v___y_586_;
v___y_574_ = v___y_589_;
v___y_575_ = v___y_588_;
v___y_576_ = v___y_587_;
v___y_577_ = v___y_590_;
v___y_578_ = v___y_591_;
v___y_579_ = v___y_592_;
v___y_580_ = v___y_593_;
v___y_581_ = v___y_594_;
v___y_582_ = v___y_595_;
v_a_583_ = v_a_598_;
goto v___jp_572_;
}
}
v___jp_599_:
{
lean_object* v___x_611_; double v___x_612_; double v___x_613_; double v___x_614_; double v___x_615_; double v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_611_ = lean_io_mono_nanos_now();
v___x_612_ = lean_float_of_nat(v___y_600_);
v___x_613_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_614_ = lean_float_div(v___x_612_, v___x_613_);
v___x_615_ = lean_float_of_nat(v___x_611_);
v___x_616_ = lean_float_div(v___x_615_, v___x_613_);
v___x_617_ = lean_box_float(v___x_614_);
v___x_618_ = lean_box_float(v___x_616_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_a_610_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
v___x_621_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4(v___y_604_, v___y_609_, v___y_605_, v___y_608_, v___y_603_, v___y_601_, v___y_607_, v___x_620_, v___y_606_, v___y_602_);
return v___x_621_;
}
v___jp_622_:
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_633_);
v___y_600_ = v___y_623_;
v___y_601_ = v___y_624_;
v___y_602_ = v___y_627_;
v___y_603_ = v___y_626_;
v___y_604_ = v___y_625_;
v___y_605_ = v___y_628_;
v___y_606_ = v___y_629_;
v___y_607_ = v___y_630_;
v___y_608_ = v___y_631_;
v___y_609_ = v___y_632_;
v_a_610_ = v___x_634_;
goto v___jp_599_;
}
v___jp_635_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(0);
v___y_623_ = v___y_636_;
v___y_624_ = v___y_637_;
v___y_625_ = v___y_640_;
v___y_626_ = v___y_639_;
v___y_627_ = v___y_638_;
v___y_628_ = v___y_641_;
v___y_629_ = v___y_642_;
v___y_630_ = v___y_643_;
v___y_631_ = v___y_644_;
v___y_632_ = v___y_645_;
v_a_633_ = v___x_646_;
goto v___jp_622_;
}
v___jp_647_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_a_658_);
v___y_600_ = v___y_648_;
v___y_601_ = v___y_649_;
v___y_602_ = v___y_652_;
v___y_603_ = v___y_651_;
v___y_604_ = v___y_650_;
v___y_605_ = v___y_653_;
v___y_606_ = v___y_654_;
v___y_607_ = v___y_655_;
v___y_608_ = v___y_656_;
v___y_609_ = v___y_657_;
v_a_610_ = v___x_659_;
goto v___jp_599_;
}
v___jp_660_:
{
if (lean_obj_tag(v___y_671_) == 0)
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___y_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___y_671_, 1);
v___y_623_ = v___y_661_;
v___y_624_ = v___y_662_;
v___y_625_ = v___y_665_;
v___y_626_ = v___y_664_;
v___y_627_ = v___y_663_;
v___y_628_ = v___y_666_;
v___y_629_ = v___y_667_;
v___y_630_ = v___y_668_;
v___y_631_ = v___y_669_;
v___y_632_ = v___y_670_;
v_a_633_ = v_a_672_;
goto v___jp_622_;
}
else
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___y_671_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___y_671_, 1);
v___y_648_ = v___y_661_;
v___y_649_ = v___y_662_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_664_;
v___y_652_ = v___y_663_;
v___y_653_ = v___y_666_;
v___y_654_ = v___y_667_;
v___y_655_ = v___y_668_;
v___y_656_ = v___y_669_;
v___y_657_ = v___y_670_;
v_a_658_ = v_a_673_;
goto v___jp_647_;
}
}
v___jp_674_:
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___redArg(v___y_676_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = l_Lean_trace_profiler_useHeartbeats;
v___x_692_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___y_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_io_mono_nanos_now();
v___x_694_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_683_, v___y_678_, v___y_676_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref_known(v___x_694_, 1);
if (lean_obj_tag(v___y_679_) == 1)
{
if (v___y_680_ == 0)
{
lean_dec_ref_known(v___y_679_, 1);
v___y_636_ = v___x_693_;
v___y_637_ = v_a_690_;
v___y_638_ = v___y_676_;
v___y_639_ = v___y_677_;
v___y_640_ = v___y_684_;
v___y_641_ = v___y_686_;
v___y_642_ = v___y_678_;
v___y_643_ = v___y_687_;
v___y_644_ = v___y_688_;
v___y_645_ = v___y_681_;
goto v___jp_635_;
}
else
{
lean_object* v_val_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_val_695_ = lean_ctor_get(v___y_679_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___y_679_, 1);
v___x_696_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_675_);
v___x_697_ = l_Lean_Name_mkStr2(v___y_675_, v___x_696_);
v___x_698_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_697_);
v___x_699_ = l_Lean_Name_append(v___x_698_, v___x_697_);
v___x_700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_685_, v___y_688_, v___x_699_);
lean_dec(v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v___x_697_);
lean_dec(v_val_695_);
v___y_636_ = v___x_693_;
v___y_637_ = v_a_690_;
v___y_638_ = v___y_676_;
v___y_639_ = v___y_677_;
v___y_640_ = v___y_684_;
v___y_641_ = v___y_686_;
v___y_642_ = v___y_678_;
v___y_643_ = v___y_687_;
v___y_644_ = v___y_688_;
v___y_645_ = v___y_681_;
goto v___jp_635_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_Elab_InfoTree_format(v_val_695_, v___x_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = l_Lean_MessageData_ofFormat(v_a_703_);
v___x_705_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___x_697_, v___x_704_, v___y_678_, v___y_676_);
v___y_661_ = v___x_693_;
v___y_662_ = v_a_690_;
v___y_663_ = v___y_676_;
v___y_664_ = v___y_677_;
v___y_665_ = v___y_684_;
v___y_666_ = v___y_686_;
v___y_667_ = v___y_678_;
v___y_668_ = v___y_687_;
v___y_669_ = v___y_688_;
v___y_670_ = v___y_681_;
v___y_671_ = v___x_705_;
goto v___jp_660_;
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_716_; 
lean_dec(v___x_697_);
v_a_706_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
v___x_708_ = v___x_702_;
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_702_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_io_error_to_string(v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 3);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_715_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = l_Lean_MessageData_ofFormat(v___x_712_);
lean_inc(v___y_682_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___y_682_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___y_648_ = v___x_693_;
v___y_649_ = v_a_690_;
v___y_650_ = v___y_684_;
v___y_651_ = v___y_677_;
v___y_652_ = v___y_676_;
v___y_653_ = v___y_686_;
v___y_654_ = v___y_678_;
v___y_655_ = v___y_687_;
v___y_656_ = v___y_688_;
v___y_657_ = v___y_681_;
v_a_658_ = v___x_714_;
goto v___jp_647_;
}
}
}
}
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v___y_679_);
v___x_717_ = lean_box(0);
v___y_623_ = v___x_693_;
v___y_624_ = v_a_690_;
v___y_625_ = v___y_684_;
v___y_626_ = v___y_677_;
v___y_627_ = v___y_676_;
v___y_628_ = v___y_686_;
v___y_629_ = v___y_678_;
v___y_630_ = v___y_687_;
v___y_631_ = v___y_688_;
v___y_632_ = v___y_681_;
v_a_633_ = v___x_717_;
goto v___jp_622_;
}
}
else
{
lean_dec(v___y_679_);
v___y_661_ = v___x_693_;
v___y_662_ = v_a_690_;
v___y_663_ = v___y_676_;
v___y_664_ = v___y_677_;
v___y_665_ = v___y_684_;
v___y_666_ = v___y_686_;
v___y_667_ = v___y_678_;
v___y_668_ = v___y_687_;
v___y_669_ = v___y_688_;
v___y_670_ = v___y_681_;
v___y_671_ = v___x_694_;
goto v___jp_660_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_io_get_num_heartbeats();
v___x_719_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_683_, v___y_678_, v___y_676_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_dec_ref_known(v___x_719_, 1);
if (lean_obj_tag(v___y_679_) == 1)
{
if (v___y_680_ == 0)
{
lean_dec_ref_known(v___y_679_, 1);
v___y_561_ = v_a_690_;
v___y_562_ = v___y_676_;
v___y_563_ = v___y_677_;
v___y_564_ = v___y_684_;
v___y_565_ = v___y_686_;
v___y_566_ = v___x_718_;
v___y_567_ = v___y_678_;
v___y_568_ = v___y_687_;
v___y_569_ = v___y_688_;
v___y_570_ = v___y_681_;
goto v___jp_560_;
}
else
{
lean_object* v_val_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_val_720_ = lean_ctor_get(v___y_679_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v___y_679_, 1);
v___x_721_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_675_);
v___x_722_ = l_Lean_Name_mkStr2(v___y_675_, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_722_);
v___x_724_ = l_Lean_Name_append(v___x_723_, v___x_722_);
v___x_725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_685_, v___y_688_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
lean_dec(v___x_722_);
lean_dec(v_val_720_);
v___y_561_ = v_a_690_;
v___y_562_ = v___y_676_;
v___y_563_ = v___y_677_;
v___y_564_ = v___y_684_;
v___y_565_ = v___y_686_;
v___y_566_ = v___x_718_;
v___y_567_ = v___y_678_;
v___y_568_ = v___y_687_;
v___y_569_ = v___y_688_;
v___y_570_ = v___y_681_;
goto v___jp_560_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = l_Lean_Elab_InfoTree_format(v_val_720_, v___x_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_MessageData_ofFormat(v_a_728_);
v___x_730_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___x_722_, v___x_729_, v___y_678_, v___y_676_);
v___y_586_ = v_a_690_;
v___y_587_ = v___y_676_;
v___y_588_ = v___y_677_;
v___y_589_ = v___y_684_;
v___y_590_ = v___y_686_;
v___y_591_ = v___x_718_;
v___y_592_ = v___y_678_;
v___y_593_ = v___y_687_;
v___y_594_ = v___y_688_;
v___y_595_ = v___y_681_;
v___y_596_ = v___x_730_;
goto v___jp_585_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_722_);
v_a_731_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v___x_727_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_io_error_to_string(v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 3);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_740_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = l_Lean_MessageData_ofFormat(v___x_737_);
lean_inc(v___y_682_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_682_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___y_573_ = v_a_690_;
v___y_574_ = v___y_684_;
v___y_575_ = v___y_677_;
v___y_576_ = v___y_676_;
v___y_577_ = v___y_686_;
v___y_578_ = v___x_718_;
v___y_579_ = v___y_678_;
v___y_580_ = v___y_687_;
v___y_581_ = v___y_688_;
v___y_582_ = v___y_681_;
v_a_583_ = v___x_739_;
goto v___jp_572_;
}
}
}
}
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v___y_679_);
v___x_742_ = lean_box(0);
v___y_548_ = v_a_690_;
v___y_549_ = v___y_684_;
v___y_550_ = v___y_677_;
v___y_551_ = v___y_676_;
v___y_552_ = v___y_686_;
v___y_553_ = v___x_718_;
v___y_554_ = v___y_678_;
v___y_555_ = v___y_687_;
v___y_556_ = v___y_688_;
v___y_557_ = v___y_681_;
v_a_558_ = v___x_742_;
goto v___jp_547_;
}
}
else
{
lean_dec(v___y_679_);
v___y_586_ = v_a_690_;
v___y_587_ = v___y_676_;
v___y_588_ = v___y_677_;
v___y_589_ = v___y_684_;
v___y_590_ = v___y_686_;
v___y_591_ = v___x_718_;
v___y_592_ = v___y_678_;
v___y_593_ = v___y_687_;
v___y_594_ = v___y_688_;
v___y_595_ = v___y_681_;
v___y_596_ = v___x_719_;
goto v___jp_585_;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___y_687_);
lean_dec(v___y_683_);
lean_dec(v___y_679_);
v_a_743_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_689_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_689_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
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
v___jp_751_:
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = l_Lean_trace_profiler;
v___x_767_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___y_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v___y_763_);
v___x_768_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_759_, v___y_754_, v___y_753_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_805_; 
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_768_, 0);
lean_dec(v_unused_806_);
v___x_770_ = v___x_768_;
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
else
{
lean_dec(v___x_768_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
if (lean_obj_tag(v___y_755_) == 1)
{
lean_del_object(v___x_770_);
if (v___y_756_ == 0)
{
lean_dec_ref_known(v___y_755_, 1);
goto v___jp_524_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_800_; 
v_val_772_ = lean_ctor_get(v___y_755_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_800_ == 0)
{
v___x_774_ = v___y_755_;
v_isShared_775_ = v_isSharedCheck_800_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v___y_755_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_800_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_752_);
v___x_777_ = l_Lean_Name_mkStr2(v___y_752_, v___x_776_);
v___x_778_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_777_);
v___x_779_ = l_Lean_Name_append(v___x_778_, v___x_777_);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_761_, v___y_764_, v___x_779_);
lean_dec(v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v___x_777_);
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
goto v___jp_524_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_box(0);
v___x_782_ = l_Lean_Elab_InfoTree_format(v_val_772_, v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_774_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l_Lean_MessageData_ofFormat(v_a_783_);
v___x_785_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___x_777_, v___x_784_, v___y_754_, v___y_753_);
return v___x_785_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_799_; 
lean_dec(v___x_777_);
v_a_786_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_799_ == 0)
{
v___x_788_ = v___x_782_;
v_isShared_789_ = v_isSharedCheck_799_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_799_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_io_error_to_string(v_a_786_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 3);
lean_ctor_set(v___x_774_, 0, v___x_790_);
v___x_792_ = v___x_774_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_798_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = l_Lean_MessageData_ofFormat(v___x_792_);
lean_inc(v___y_758_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___y_758_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_794_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
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
lean_dec(v___y_755_);
v___x_801_ = lean_box(0);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_801_);
v___x_803_ = v___x_770_;
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
lean_dec(v___y_755_);
return v___x_768_;
}
}
else
{
v___y_675_ = v___y_752_;
v___y_676_ = v___y_753_;
v___y_677_ = v_a_765_;
v___y_678_ = v___y_754_;
v___y_679_ = v___y_755_;
v___y_680_ = v___y_756_;
v___y_681_ = v___y_757_;
v___y_682_ = v___y_758_;
v___y_683_ = v___y_759_;
v___y_684_ = v___y_760_;
v___y_685_ = v___y_761_;
v___y_686_ = v___y_762_;
v___y_687_ = v___y_763_;
v___y_688_ = v___y_764_;
goto v___jp_674_;
}
}
v_resetjp_809_:
{
lean_object* v_desc_812_; lean_object* v_diagnostics_813_; lean_object* v_infoTree_x3f_814_; lean_object* v_desc_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___x_894_; 
v_desc_812_ = lean_ctor_get(v_element_807_, 0);
lean_inc_ref(v_desc_812_);
v_diagnostics_813_ = lean_ctor_get(v_element_807_, 1);
lean_inc_ref(v_diagnostics_813_);
v_infoTree_x3f_814_ = lean_ctor_get(v_element_807_, 2);
lean_inc(v_infoTree_x3f_814_);
lean_dec_ref(v_element_807_);
v___x_894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_894_, 0, v_desc_812_);
switch(lean_obj_tag(v_range_x3f_516_))
{
case 0:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 5);
lean_ctor_set(v___x_810_, 1, v___x_895_);
lean_ctor_set(v___x_810_, 0, v___x_894_);
v___x_897_ = v___x_810_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
v_desc_816_ = v___x_897_;
v___y_817_ = v_a_518_;
v___y_818_ = v_a_519_;
goto v___jp_815_;
}
}
case 1:
{
lean_object* v_range_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_959_; 
v_range_899_ = lean_ctor_get(v_range_x3f_516_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_range_x3f_516_);
if (v_isSharedCheck_959_ == 0)
{
v___x_901_ = v_range_x3f_516_;
v_isShared_902_ = v_isSharedCheck_959_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_range_899_);
lean_dec(v_range_x3f_516_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_959_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_fileMap_903_; lean_object* v_start_904_; lean_object* v_stop_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_958_; 
v_fileMap_903_ = lean_ctor_get(v_a_518_, 1);
v_start_904_ = lean_ctor_get(v_range_899_, 0);
v_stop_905_ = lean_ctor_get(v_range_899_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_range_899_);
if (v_isSharedCheck_958_ == 0)
{
v___x_907_ = v_range_899_;
v_isShared_908_ = v_isSharedCheck_958_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_stop_905_);
lean_inc(v_start_904_);
lean_dec(v_range_899_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_958_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v_line_910_; lean_object* v_column_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_957_; 
lean_inc_ref(v_fileMap_903_);
v___x_909_ = l_Lean_FileMap_toPosition(v_fileMap_903_, v_start_904_);
lean_dec(v_start_904_);
v_line_910_ = lean_ctor_get(v___x_909_, 0);
v_column_911_ = lean_ctor_get(v___x_909_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_957_ == 0)
{
v___x_913_ = v___x_909_;
v_isShared_914_ = v_isSharedCheck_957_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_column_911_);
lean_inc(v_line_910_);
lean_dec(v___x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_957_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v_line_916_; lean_object* v_column_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_956_; 
lean_inc_ref(v_fileMap_903_);
v___x_915_ = l_Lean_FileMap_toPosition(v_fileMap_903_, v_stop_905_);
lean_dec(v_stop_905_);
v_line_916_ = lean_ctor_get(v___x_915_, 0);
v_column_917_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_956_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_956_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_column_917_);
lean_inc(v_line_916_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_956_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_922_ = l_Nat_reprFast(v_line_910_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 3);
lean_ctor_set(v___x_901_, 0, v___x_922_);
v___x_924_ = v___x_901_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_955_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 5);
lean_ctor_set(v___x_919_, 1, v___x_924_);
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_926_ = v___x_919_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_954_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 5);
lean_ctor_set(v___x_913_, 1, v___x_927_);
lean_ctor_set(v___x_913_, 0, v___x_926_);
v___x_929_ = v___x_913_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_953_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = l_Nat_reprFast(v_column_911_);
v___x_931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 5);
lean_ctor_set(v___x_907_, 1, v___x_931_);
lean_ctor_set(v___x_907_, 0, v___x_929_);
v___x_933_ = v___x_907_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_952_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 5);
lean_ctor_set(v___x_810_, 1, v___x_934_);
lean_ctor_set(v___x_810_, 0, v___x_933_);
v___x_936_ = v___x_810_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_934_);
v___x_936_ = v_reuseFailAlloc_951_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Nat_reprFast(v_line_916_);
v___x_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_921_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_927_);
v___x_943_ = l_Nat_reprFast(v_column_917_);
v___x_944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_942_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_934_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_938_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_894_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v_desc_816_ = v___x_950_;
v___y_817_ = v_a_518_;
v___y_818_ = v_a_519_;
goto v___jp_815_;
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
default: 
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 5);
lean_ctor_set(v___x_810_, 1, v___x_960_);
lean_ctor_set(v___x_810_, 0, v___x_894_);
v___x_962_ = v___x_810_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_desc_816_ = v___x_962_;
v___y_817_ = v_a_518_;
v___y_818_ = v_a_519_;
goto v___jp_815_;
}
}
}
v___jp_815_:
{
lean_object* v_msgLog_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_892_; 
v_msgLog_819_ = lean_ctor_get(v_diagnostics_813_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_diagnostics_813_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_diagnostics_813_, 1);
lean_dec(v_unused_893_);
v___x_821_ = v_diagnostics_813_;
v_isShared_822_ = v_isSharedCheck_892_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_msgLog_819_);
lean_dec(v_diagnostics_813_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_892_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_MessageLog_toList(v_msgLog_819_);
lean_dec_ref(v_msgLog_819_);
v___x_824_ = lean_box(0);
v___x_825_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_823_, v___x_824_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_options_826_; lean_object* v_a_827_; lean_object* v_ref_828_; lean_object* v_inheritedTraceOptions_829_; uint8_t v_hasTrace_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_options_826_ = lean_ctor_get(v___y_817_, 2);
v_a_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_825_, 1);
v_ref_828_ = lean_ctor_get(v___y_817_, 5);
v_inheritedTraceOptions_829_ = lean_ctor_get(v___y_817_, 13);
v_hasTrace_830_ = lean_ctor_get_uint8(v_options_826_, sizeof(void*)*1);
v___x_831_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_832_ = lean_array_to_list(v_children_808_);
v___x_833_ = lean_bool_not(v_hasTrace_830_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_835_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_834_, v_a_827_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 5);
lean_ctor_set(v___x_821_, 1, v___x_835_);
lean_ctor_set(v___x_821_, 0, v_desc_816_);
v___x_837_ = v___x_821_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_desc_816_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_835_);
v___x_837_ = v_reuseFailAlloc_844_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___f_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; 
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_838_, 0, v___x_837_);
v___x_839_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_840_ = 1;
v___x_841_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
if (v_hasTrace_830_ == 0)
{
v___y_752_ = v___x_831_;
v___y_753_ = v___y_818_;
v___y_754_ = v___y_817_;
v___y_755_ = v_infoTree_x3f_814_;
v___y_756_ = v_hasTrace_830_;
v___y_757_ = v___x_840_;
v___y_758_ = v_ref_828_;
v___y_759_ = v___x_832_;
v___y_760_ = v___x_839_;
v___y_761_ = v_inheritedTraceOptions_829_;
v___y_762_ = v___x_841_;
v___y_763_ = v___f_838_;
v___y_764_ = v_options_826_;
v_a_765_ = v_hasTrace_830_;
goto v___jp_751_;
}
else
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_829_, v_options_826_, v___x_842_);
if (v___x_843_ == 0)
{
v___y_752_ = v___x_831_;
v___y_753_ = v___y_818_;
v___y_754_ = v___y_817_;
v___y_755_ = v_infoTree_x3f_814_;
v___y_756_ = v_hasTrace_830_;
v___y_757_ = v___x_840_;
v___y_758_ = v_ref_828_;
v___y_759_ = v___x_832_;
v___y_760_ = v___x_839_;
v___y_761_ = v_inheritedTraceOptions_829_;
v___y_762_ = v___x_841_;
v___y_763_ = v___f_838_;
v___y_764_ = v_options_826_;
v_a_765_ = v___x_843_;
goto v___jp_751_;
}
else
{
v___y_675_ = v___x_831_;
v___y_676_ = v___y_818_;
v___y_677_ = v___x_843_;
v___y_678_ = v___y_817_;
v___y_679_ = v_infoTree_x3f_814_;
v___y_680_ = v_hasTrace_830_;
v___y_681_ = v___x_840_;
v___y_682_ = v_ref_828_;
v___y_683_ = v___x_832_;
v___y_684_ = v___x_839_;
v___y_685_ = v_inheritedTraceOptions_829_;
v___y_686_ = v___x_841_;
v___y_687_ = v___f_838_;
v___y_688_ = v_options_826_;
goto v___jp_674_;
}
}
}
}
else
{
lean_object* v___x_845_; 
lean_dec(v_a_827_);
lean_dec(v_desc_816_);
v___x_845_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___x_832_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_883_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_882_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_882_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_infoTree_x3f_814_) == 1)
{
lean_del_object(v___x_847_);
if (v_hasTrace_830_ == 0)
{
lean_dec_ref_known(v_infoTree_x3f_814_, 1);
lean_del_object(v___x_821_);
goto v___jp_521_;
}
else
{
lean_object* v_val_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_877_; 
v_val_849_ = lean_ctor_get(v_infoTree_x3f_814_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_infoTree_x3f_814_);
if (v_isSharedCheck_877_ == 0)
{
v___x_851_ = v_infoTree_x3f_814_;
v_isShared_852_ = v_isSharedCheck_877_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_val_849_);
lean_dec(v_infoTree_x3f_814_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_877_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_854_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_829_, v_options_826_, v___x_854_);
if (v___x_855_ == 0)
{
lean_del_object(v___x_851_);
lean_dec(v_val_849_);
lean_del_object(v___x_821_);
goto v___jp_521_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_box(0);
v___x_857_ = l_Lean_Elab_InfoTree_format(v_val_849_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_del_object(v___x_851_);
lean_del_object(v___x_821_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_MessageData_ofFormat(v_a_858_);
v___x_860_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___x_853_, v___x_859_, v___y_817_, v___y_818_);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_876_; 
v_a_861_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_876_ == 0)
{
v___x_863_ = v___x_857_;
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_io_error_to_string(v_a_861_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 3);
lean_ctor_set(v___x_851_, 0, v___x_865_);
v___x_867_ = v___x_851_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_875_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_MessageData_ofFormat(v___x_867_);
lean_inc(v_ref_828_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_868_);
lean_ctor_set(v___x_821_, 0, v_ref_828_);
v___x_870_ = v___x_821_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_ref_828_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_870_);
v___x_872_ = v___x_863_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
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
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_del_object(v___x_821_);
lean_dec(v_infoTree_x3f_814_);
v___x_878_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_878_);
v___x_880_ = v___x_847_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_del_object(v___x_821_);
lean_dec(v_infoTree_x3f_814_);
return v___x_845_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_821_);
lean_dec(v_desc_816_);
lean_dec(v_infoTree_x3f_814_);
lean_dec_ref(v_children_808_);
v_a_884_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_825_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_825_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(lean_object* v_as_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
if (lean_obj_tag(v_as_965_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
else
{
lean_object* v_head_971_; lean_object* v_tail_972_; lean_object* v_reportingRange_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_head_971_ = lean_ctor_get(v_as_965_, 0);
lean_inc(v_head_971_);
v_tail_972_ = lean_ctor_get(v_as_965_, 1);
lean_inc(v_tail_972_);
lean_dec_ref_known(v_as_965_, 2);
v_reportingRange_973_ = lean_ctor_get(v_head_971_, 1);
lean_inc(v_reportingRange_973_);
v___x_974_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_971_);
v___x_975_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_973_, v___x_974_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref_known(v___x_975_, 1);
v_as_965_ = v_tail_972_;
goto _start;
}
else
{
lean_dec(v_tail_972_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5___boxed(lean_object* v_as_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_as_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_982_, lean_object* v_s_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_982_, v_s_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_988_, v_x_989_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_994_, v_x_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6(lean_object* v_00_u03b1_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___redArg(v_x_1001_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4_spec__6(v_00_u03b1_1006_, v_x_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_box(2);
v___x_1017_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_1016_, v_s_1012_, v_a_1013_, v_a_1014_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Language_SnapshotTree_trace(v_s_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1022_;
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

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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
lean_ctor_set(v___x_89_, 3, v___x_88_);
lean_ctor_set(v___x_89_, 4, v___x_87_);
lean_ctor_set(v___x_89_, 5, v___x_87_);
lean_ctor_set(v___x_89_, 6, v___x_87_);
lean_ctor_set(v___x_89_, 7, v___x_87_);
lean_ctor_set(v___x_89_, 8, v___x_87_);
lean_ctor_set(v___x_89_, 9, v___x_87_);
lean_ctor_set(v___x_89_, 10, v___x_87_);
lean_ctor_set(v___x_89_, 11, v___x_86_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(32u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__3);
v___x_98_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_94_);
lean_ctor_set(v___x_98_, 3, v___x_94_);
lean_ctor_set_usize(v___x_98_, 4, v___x_93_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_box(1);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__4);
v___x_101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__1);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_toCold_108_; lean_object* v_env_109_; lean_object* v_options_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_toCold_108_ = lean_ctor_get(v___y_104_, 0);
v_env_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_107_);
v_options_110_ = lean_ctor_get(v_toCold_108_, 2);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_109_, v___x_111_);
v___x_113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__2);
v___x_114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_110_);
v___x_115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_115_, 0, v_env_112_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
lean_ctor_set(v___x_115_, 3, v_options_110_);
v___x_116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_msgData_103_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2___boxed(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msgData_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_122_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_123_; double v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_float_of_nat(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(lean_object* v_cls_128_, lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_ref_133_; lean_object* v___x_134_; lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_180_; 
v_ref_133_ = lean_ctor_get(v___y_130_, 2);
v___x_134_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_129_, v___y_130_, v___y_131_);
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_180_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_180_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_180_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v_traceState_140_; lean_object* v_env_141_; lean_object* v_nextMacroScope_142_; lean_object* v_ngen_143_; lean_object* v_auxDeclNGen_144_; lean_object* v_cache_145_; lean_object* v_recordedDeps_146_; lean_object* v_messages_147_; lean_object* v_infoState_148_; lean_object* v_snapshotTasks_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_179_; 
v___x_139_ = lean_st_ref_take(v___y_131_);
v_traceState_140_ = lean_ctor_get(v___x_139_, 4);
v_env_141_ = lean_ctor_get(v___x_139_, 0);
v_nextMacroScope_142_ = lean_ctor_get(v___x_139_, 1);
v_ngen_143_ = lean_ctor_get(v___x_139_, 2);
v_auxDeclNGen_144_ = lean_ctor_get(v___x_139_, 3);
v_cache_145_ = lean_ctor_get(v___x_139_, 5);
v_recordedDeps_146_ = lean_ctor_get(v___x_139_, 6);
v_messages_147_ = lean_ctor_get(v___x_139_, 7);
v_infoState_148_ = lean_ctor_get(v___x_139_, 8);
v_snapshotTasks_149_ = lean_ctor_get(v___x_139_, 9);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_179_ == 0)
{
v___x_151_ = v___x_139_;
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_snapshotTasks_149_);
lean_inc(v_infoState_148_);
lean_inc(v_messages_147_);
lean_inc(v_recordedDeps_146_);
lean_inc(v_cache_145_);
lean_inc(v_traceState_140_);
lean_inc(v_auxDeclNGen_144_);
lean_inc(v_ngen_143_);
lean_inc(v_nextMacroScope_142_);
lean_inc(v_env_141_);
lean_dec(v___x_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint64_t v_tid_153_; lean_object* v_traces_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_178_; 
v_tid_153_ = lean_ctor_get_uint64(v_traceState_140_, sizeof(void*)*1);
v_traces_154_ = lean_ctor_get(v_traceState_140_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_traceState_140_);
if (v_isSharedCheck_178_ == 0)
{
v___x_156_ = v_traceState_140_;
v_isShared_157_ = v_isSharedCheck_178_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_traces_154_);
lean_dec(v_traceState_140_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_178_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; double v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_box(0);
v___x_160_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
v___x_161_ = 0;
v___x_162_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_163_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_163_, 0, v_cls_128_);
lean_ctor_set(v___x_163_, 1, v___x_159_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
lean_ctor_set_float(v___x_163_, sizeof(void*)*3, v___x_160_);
lean_ctor_set_float(v___x_163_, sizeof(void*)*3 + 8, v___x_160_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*3 + 16, v___x_161_);
v___x_164_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__2));
v___x_165_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v_a_135_);
lean_ctor_set(v___x_165_, 2, v___x_164_);
lean_inc(v_ref_133_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_ref_133_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_PersistentArray_push___redArg(v_traces_154_, v___x_166_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_167_);
v___x_169_ = v___x_156_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_167_);
lean_ctor_set_uint64(v_reuseFailAlloc_177_, sizeof(void*)*1, v_tid_153_);
v___x_169_ = v_reuseFailAlloc_177_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_169_);
v___x_171_ = v___x_151_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_env_141_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_nextMacroScope_142_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_ngen_143_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_auxDeclNGen_144_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v_cache_145_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_recordedDeps_146_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_messages_147_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_infoState_148_);
lean_ctor_set(v_reuseFailAlloc_176_, 9, v_snapshotTasks_149_);
v___x_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_st_ref_put(v___y_131_, v___x_171_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_158_);
v___x_174_ = v___x_137_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_158_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___boxed(lean_object* v_cls_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v_cls_181_, v_msg_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(lean_object* v_pre_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_dec(v_pre_187_);
return v_x_188_;
}
else
{
lean_object* v_head_190_; lean_object* v_tail_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v_head_190_ = lean_ctor_get(v_x_189_, 0);
v_tail_191_ = lean_ctor_get(v_x_189_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v_x_189_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_tail_191_);
lean_inc(v_head_190_);
lean_dec(v_x_189_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
lean_inc(v_pre_187_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 5);
lean_ctor_set(v___x_193_, 1, v_pre_187_);
lean_ctor_set(v___x_193_, 0, v_x_188_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_x_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_pre_187_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v_head_190_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v_x_188_ = v___x_198_;
v_x_189_ = v_tail_191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(lean_object* v_pre_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_204_; 
lean_dec(v_pre_202_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_head_205_; lean_object* v_tail_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_head_205_ = lean_ctor_get(v_x_203_, 0);
v_tail_206_ = lean_ctor_get(v_x_203_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_tail_206_);
lean_inc(v_head_205_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v_head_205_);
lean_inc(v_pre_202_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 5);
lean_ctor_set(v___x_208_, 1, v___x_210_);
lean_ctor_set(v___x_208_, 0, v_pre_202_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_pre_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3_spec__4(v_pre_202_, v___x_212_, v_tail_206_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_List_reverse___redArg(v_x_217_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v_head_221_ = lean_ctor_get(v_x_216_, 0);
v_tail_222_ = lean_ctor_get(v_x_216_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_232_ == 0)
{
v___x_224_ = v_x_216_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_x_216_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = 0;
v___x_227_ = l_Lean_Message_toString(v_head_221_, v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_x_217_);
lean_ctor_set(v___x_224_, 0, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_x_217_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v_x_216_ = v_tail_222_;
v_x_217_ = v___x_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg___boxed(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_233_, v_x_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v_x_237_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v_x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v_x_237_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v_x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 0);
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg___boxed(lean_object* v_x_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(lean_object* v_opts_258_, lean_object* v_opt_259_){
_start:
{
lean_object* v_name_260_; lean_object* v_defValue_261_; lean_object* v_map_262_; lean_object* v___x_263_; 
v_name_260_ = lean_ctor_get(v_opt_259_, 0);
v_defValue_261_ = lean_ctor_get(v_opt_259_, 1);
v_map_262_ = lean_ctor_get(v_opts_258_, 0);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_262_, v_name_260_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_inc(v_defValue_261_);
return v_defValue_261_;
}
else
{
lean_object* v_val_264_; 
v_val_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_263_, 1);
if (lean_obj_tag(v_val_264_) == 3)
{
lean_object* v_v_265_; 
v_v_265_ = lean_ctor_get(v_val_264_, 0);
lean_inc(v_v_265_);
lean_dec_ref_known(v_val_264_, 1);
return v_v_265_;
}
else
{
lean_dec(v_val_264_);
lean_inc(v_defValue_261_);
return v_defValue_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11___boxed(lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_266_, v_opt_267_);
lean_dec_ref(v_opt_267_);
lean_dec_ref(v_opts_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(size_t v_sz_269_, size_t v_i_270_, lean_object* v_bs_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_lt(v_i_270_, v_sz_269_);
if (v___x_272_ == 0)
{
return v_bs_271_;
}
else
{
lean_object* v_v_273_; lean_object* v_msg_274_; lean_object* v___x_275_; lean_object* v_bs_x27_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_v_273_ = lean_array_uget_borrowed(v_bs_271_, v_i_270_);
v_msg_274_ = lean_ctor_get(v_v_273_, 1);
lean_inc_ref(v_msg_274_);
v___x_275_ = lean_unsigned_to_nat(0u);
v_bs_x27_276_ = lean_array_uset(v_bs_271_, v_i_270_, v___x_275_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_270_, v___x_277_);
v___x_279_ = lean_array_uset(v_bs_x27_276_, v_i_270_, v_msg_274_);
v_i_270_ = v___x_278_;
v_bs_271_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_281_, lean_object* v_i_282_, lean_object* v_bs_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_281_);
lean_dec(v_sz_281_);
v_i_boxed_285_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_boxed_284_, v_i_boxed_285_, v_bs_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(lean_object* v_oldTraces_287_, lean_object* v_data_288_, lean_object* v_ref_289_, lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_toCold_294_; lean_object* v_currRecDepth_295_; lean_object* v_ref_296_; uint16_t v_optionFlags_297_; uint8_t v_suppressElabErrors_298_; uint8_t v_isRecordingDeps_299_; lean_object* v_ref_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_traces_304_; lean_object* v___x_305_; size_t v_sz_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v_msg_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_349_; 
v_toCold_294_ = lean_ctor_get(v___y_291_, 0);
v_currRecDepth_295_ = lean_ctor_get(v___y_291_, 1);
v_ref_296_ = lean_ctor_get(v___y_291_, 2);
v_optionFlags_297_ = lean_ctor_get_uint16(v___y_291_, sizeof(void*)*3);
v_suppressElabErrors_298_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 2);
v_isRecordingDeps_299_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 3);
v_ref_300_ = l_Lean_replaceRef(v_ref_289_, v_ref_296_);
lean_inc(v_currRecDepth_295_);
lean_inc_ref(v_toCold_294_);
v___x_301_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_301_, 0, v_toCold_294_);
lean_ctor_set(v___x_301_, 1, v_currRecDepth_295_);
lean_ctor_set(v___x_301_, 2, v_ref_300_);
lean_ctor_set_uint16(v___x_301_, sizeof(void*)*3, v_optionFlags_297_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*3 + 2, v_suppressElabErrors_298_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*3 + 3, v_isRecordingDeps_299_);
v___x_302_ = lean_st_ref_get(v___y_292_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
lean_inc_ref(v_traceState_303_);
lean_dec(v___x_302_);
v_traces_304_ = lean_ctor_get(v_traceState_303_, 0);
lean_inc_ref(v_traces_304_);
lean_dec_ref(v_traceState_303_);
v___x_305_ = l_Lean_PersistentArray_toArray___redArg(v_traces_304_);
lean_dec_ref(v_traces_304_);
v_sz_306_ = lean_array_size(v___x_305_);
v___x_307_ = ((size_t)0ULL);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8_spec__9(v_sz_306_, v___x_307_, v___x_305_);
v_msg_309_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_309_, 0, v_data_288_);
lean_ctor_set(v_msg_309_, 1, v_msg_290_);
lean_ctor_set(v_msg_309_, 2, v___x_308_);
v___x_310_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2_spec__2(v_msg_309_, v___x_301_, v___y_292_);
lean_dec_ref_known(v___x_301_, 3);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_349_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_349_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_349_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v_traceState_316_; lean_object* v_env_317_; lean_object* v_nextMacroScope_318_; lean_object* v_ngen_319_; lean_object* v_auxDeclNGen_320_; lean_object* v_cache_321_; lean_object* v_recordedDeps_322_; lean_object* v_messages_323_; lean_object* v_infoState_324_; lean_object* v_snapshotTasks_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_348_; 
v___x_315_ = lean_st_ref_take(v___y_292_);
v_traceState_316_ = lean_ctor_get(v___x_315_, 4);
v_env_317_ = lean_ctor_get(v___x_315_, 0);
v_nextMacroScope_318_ = lean_ctor_get(v___x_315_, 1);
v_ngen_319_ = lean_ctor_get(v___x_315_, 2);
v_auxDeclNGen_320_ = lean_ctor_get(v___x_315_, 3);
v_cache_321_ = lean_ctor_get(v___x_315_, 5);
v_recordedDeps_322_ = lean_ctor_get(v___x_315_, 6);
v_messages_323_ = lean_ctor_get(v___x_315_, 7);
v_infoState_324_ = lean_ctor_get(v___x_315_, 8);
v_snapshotTasks_325_ = lean_ctor_get(v___x_315_, 9);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_348_ == 0)
{
v___x_327_ = v___x_315_;
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snapshotTasks_325_);
lean_inc(v_infoState_324_);
lean_inc(v_messages_323_);
lean_inc(v_recordedDeps_322_);
lean_inc(v_cache_321_);
lean_inc(v_traceState_316_);
lean_inc(v_auxDeclNGen_320_);
lean_inc(v_ngen_319_);
lean_inc(v_nextMacroScope_318_);
lean_inc(v_env_317_);
lean_dec(v___x_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint64_t v_tid_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_346_; 
v_tid_329_ = lean_ctor_get_uint64(v_traceState_316_, sizeof(void*)*1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_traceState_316_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v_traceState_316_, 0);
lean_dec(v_unused_347_);
v___x_331_ = v_traceState_316_;
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_traceState_316_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_289_);
lean_ctor_set(v___x_334_, 1, v_a_311_);
v___x_335_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_287_, v___x_334_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_335_);
v___x_337_ = v___x_331_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_335_);
lean_ctor_set_uint64(v_reuseFailAlloc_345_, sizeof(void*)*1, v_tid_329_);
v___x_337_ = v_reuseFailAlloc_345_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 4, v___x_337_);
v___x_339_ = v___x_327_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_env_317_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_nextMacroScope_318_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_ngen_319_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_auxDeclNGen_320_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v_cache_321_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_recordedDeps_322_);
lean_ctor_set(v_reuseFailAlloc_344_, 7, v_messages_323_);
lean_ctor_set(v_reuseFailAlloc_344_, 8, v_infoState_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 9, v_snapshotTasks_325_);
v___x_339_ = v_reuseFailAlloc_344_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_st_ref_put(v___y_292_, v___x_339_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_333_);
v___x_342_ = v___x_313_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_333_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8___boxed(lean_object* v_oldTraces_350_, lean_object* v_data_351_, lean_object* v_ref_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_350_, v_data_351_, v_ref_352_, v_msg_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(lean_object* v_e_358_){
_start:
{
if (lean_obj_tag(v_e_358_) == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 2;
return v___x_359_;
}
else
{
uint8_t v___x_360_; 
v___x_360_ = 0;
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10___boxed(lean_object* v_e_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_e_361_);
lean_dec_ref(v_e_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_367_; double v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(1000u);
v___x_368_ = lean_float_of_nat(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(lean_object* v_cls_369_, uint8_t v_collapsed_370_, lean_object* v_tag_371_, lean_object* v_opts_372_, uint8_t v_clsEnabled_373_, lean_object* v_oldTraces_374_, lean_object* v_msg_375_, lean_object* v_resStartStop_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v_data_385_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___y_393_; lean_object* v_a_394_; uint8_t v___y_409_; double v___y_441_; 
v_fst_380_ = lean_ctor_get(v_resStartStop_376_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v_resStartStop_376_, 1);
lean_inc(v_snd_381_);
lean_dec_ref(v_resStartStop_376_);
v_fst_388_ = lean_ctor_get(v_snd_381_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v_snd_381_, 1);
lean_inc(v_snd_389_);
lean_dec(v_snd_381_);
v___x_390_ = l_Lean_trace_profiler;
v___x_391_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_372_, v___x_390_);
if (v___x_391_ == 0)
{
v___y_409_ = v___x_391_;
goto v___jp_408_;
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = l_Lean_trace_profiler_useHeartbeats;
v___x_447_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_opts_372_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; double v___x_450_; double v___x_451_; double v___x_452_; 
v___x_448_ = l_Lean_trace_profiler_threshold;
v___x_449_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_372_, v___x_448_);
v___x_450_ = lean_float_of_nat(v___x_449_);
v___x_451_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__2);
v___x_452_ = lean_float_div(v___x_450_, v___x_451_);
v___y_441_ = v___x_452_;
goto v___jp_440_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; double v___x_455_; 
v___x_453_ = l_Lean_trace_profiler_threshold;
v___x_454_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__11(v_opts_372_, v___x_453_);
v___x_455_ = lean_float_of_nat(v___x_454_);
v___y_441_ = v___x_455_;
goto v___jp_440_;
}
}
v___jp_382_:
{
lean_object* v___x_386_; 
lean_inc(v___y_383_);
v___x_386_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__8(v_oldTraces_374_, v_data_385_, v___y_383_, v___y_384_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; 
lean_dec_ref_known(v___x_386_, 1);
v___x_387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_380_);
return v___x_387_;
}
else
{
lean_dec(v_fst_380_);
return v___x_386_;
}
}
v___jp_392_:
{
uint8_t v_result_395_; lean_object* v___x_396_; lean_object* v___x_397_; double v___x_398_; lean_object* v_data_399_; 
v_result_395_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__10(v_fst_380_);
v___x_396_ = lean_box(v_result_395_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__0);
lean_inc_ref(v_tag_371_);
lean_inc_ref(v___x_397_);
lean_inc(v_cls_369_);
v_data_399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_399_, 0, v_cls_369_);
lean_ctor_set(v_data_399_, 1, v___x_397_);
lean_ctor_set(v_data_399_, 2, v_tag_371_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3, v___x_398_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3 + 8, v___x_398_);
lean_ctor_set_uint8(v_data_399_, sizeof(void*)*3 + 16, v_collapsed_370_);
if (v___x_391_ == 0)
{
lean_dec_ref_known(v___x_397_, 1);
lean_dec(v_snd_389_);
lean_dec(v_fst_388_);
lean_dec_ref(v_tag_371_);
lean_dec(v_cls_369_);
v___y_383_ = v___y_393_;
v___y_384_ = v_a_394_;
v_data_385_ = v_data_399_;
goto v___jp_382_;
}
else
{
lean_object* v_data_400_; double v___x_401_; double v___x_402_; 
lean_dec_ref_known(v_data_399_, 3);
v_data_400_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_400_, 0, v_cls_369_);
lean_ctor_set(v_data_400_, 1, v___x_397_);
lean_ctor_set(v_data_400_, 2, v_tag_371_);
v___x_401_ = lean_unbox_float(v_fst_388_);
lean_dec(v_fst_388_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3, v___x_401_);
v___x_402_ = lean_unbox_float(v_snd_389_);
lean_dec(v_snd_389_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3 + 8, v___x_402_);
lean_ctor_set_uint8(v_data_400_, sizeof(void*)*3 + 16, v_collapsed_370_);
v___y_383_ = v___y_393_;
v___y_384_ = v_a_394_;
v_data_385_ = v_data_400_;
goto v___jp_382_;
}
}
v___jp_403_:
{
lean_object* v_ref_404_; lean_object* v___x_405_; 
v_ref_404_ = lean_ctor_get(v___y_377_, 2);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
lean_inc(v_fst_380_);
v___x_405_ = lean_apply_4(v_msg_375_, v_fst_380_, v___y_377_, v___y_378_, lean_box(0));
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___y_393_ = v_ref_404_;
v_a_394_ = v_a_406_;
goto v___jp_392_;
}
else
{
lean_object* v___x_407_; 
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___closed__1);
v___y_393_ = v_ref_404_;
v_a_394_ = v___x_407_;
goto v___jp_392_;
}
}
v___jp_408_:
{
if (v_clsEnabled_373_ == 0)
{
if (v___y_409_ == 0)
{
lean_object* v___x_410_; lean_object* v_traceState_411_; lean_object* v_env_412_; lean_object* v_nextMacroScope_413_; lean_object* v_ngen_414_; lean_object* v_auxDeclNGen_415_; lean_object* v_cache_416_; lean_object* v_recordedDeps_417_; lean_object* v_messages_418_; lean_object* v_infoState_419_; lean_object* v_snapshotTasks_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_snd_389_);
lean_dec(v_fst_388_);
lean_dec_ref(v_msg_375_);
lean_dec_ref(v_tag_371_);
lean_dec(v_cls_369_);
v___x_410_ = lean_st_ref_take(v___y_378_);
v_traceState_411_ = lean_ctor_get(v___x_410_, 4);
v_env_412_ = lean_ctor_get(v___x_410_, 0);
v_nextMacroScope_413_ = lean_ctor_get(v___x_410_, 1);
v_ngen_414_ = lean_ctor_get(v___x_410_, 2);
v_auxDeclNGen_415_ = lean_ctor_get(v___x_410_, 3);
v_cache_416_ = lean_ctor_get(v___x_410_, 5);
v_recordedDeps_417_ = lean_ctor_get(v___x_410_, 6);
v_messages_418_ = lean_ctor_get(v___x_410_, 7);
v_infoState_419_ = lean_ctor_get(v___x_410_, 8);
v_snapshotTasks_420_ = lean_ctor_get(v___x_410_, 9);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_439_ == 0)
{
v___x_422_ = v___x_410_;
v_isShared_423_ = v_isSharedCheck_439_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snapshotTasks_420_);
lean_inc(v_infoState_419_);
lean_inc(v_messages_418_);
lean_inc(v_recordedDeps_417_);
lean_inc(v_cache_416_);
lean_inc(v_traceState_411_);
lean_inc(v_auxDeclNGen_415_);
lean_inc(v_ngen_414_);
lean_inc(v_nextMacroScope_413_);
lean_inc(v_env_412_);
lean_dec(v___x_410_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_439_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint64_t v_tid_424_; lean_object* v_traces_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_438_; 
v_tid_424_ = lean_ctor_get_uint64(v_traceState_411_, sizeof(void*)*1);
v_traces_425_ = lean_ctor_get(v_traceState_411_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_traceState_411_);
if (v_isSharedCheck_438_ == 0)
{
v___x_427_ = v_traceState_411_;
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_traces_425_);
lean_dec(v_traceState_411_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_374_, v_traces_425_);
lean_dec_ref(v_traces_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_429_);
lean_ctor_set_uint64(v_reuseFailAlloc_437_, sizeof(void*)*1, v_tid_424_);
v___x_431_ = v_reuseFailAlloc_437_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 4, v___x_431_);
v___x_433_ = v___x_422_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_env_412_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_413_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ngen_414_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_415_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_cache_416_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_recordedDeps_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_messages_418_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_infoState_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 9, v_snapshotTasks_420_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_st_ref_put(v___y_378_, v___x_433_);
v___x_435_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_fst_380_);
return v___x_435_;
}
}
}
}
}
else
{
goto v___jp_403_;
}
}
else
{
goto v___jp_403_;
}
}
v___jp_440_:
{
double v___x_442_; double v___x_443_; double v___x_444_; uint8_t v___x_445_; 
v___x_442_ = lean_unbox_float(v_snd_389_);
v___x_443_ = lean_unbox_float(v_fst_388_);
v___x_444_ = lean_float_sub(v___x_442_, v___x_443_);
v___x_445_ = lean_float_decLt(v___y_441_, v___x_444_);
v___y_409_ = v___x_445_;
goto v___jp_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6___boxed(lean_object* v_cls_456_, lean_object* v_collapsed_457_, lean_object* v_tag_458_, lean_object* v_opts_459_, lean_object* v_clsEnabled_460_, lean_object* v_oldTraces_461_, lean_object* v_msg_462_, lean_object* v_resStartStop_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v_collapsed_boxed_467_; uint8_t v_clsEnabled_boxed_468_; lean_object* v_res_469_; 
v_collapsed_boxed_467_ = lean_unbox(v_collapsed_457_);
v_clsEnabled_boxed_468_ = lean_unbox(v_clsEnabled_460_);
v_res_469_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v_cls_456_, v_collapsed_boxed_467_, v_tag_458_, v_opts_459_, v_clsEnabled_boxed_468_, v_oldTraces_461_, v_msg_462_, v_resStartStop_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec_ref(v_opts_459_);
return v_res_469_;
}
}
static double _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0(void){
_start:
{
lean_object* v___x_470_; double v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(1000000000u);
v___x_471_ = lean_float_of_nat(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_485_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_486_ = l_Lean_Name_append(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_491_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
v___x_492_ = l_Lean_Name_append(v___x_491_, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(lean_object* v_range_x3f_514_, lean_object* v_s_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v_a_530_; uint8_t v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v_a_550_; uint8_t v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v_a_563_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; uint8_t v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v_a_590_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v_a_613_; lean_object* v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v_a_626_; lean_object* v___y_629_; uint8_t v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v_element_720_; lean_object* v_children_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_887_; 
v_element_720_ = lean_ctor_get(v_s_515_, 0);
v_children_721_ = lean_ctor_get(v_s_515_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_s_515_);
if (v_isSharedCheck_887_ == 0)
{
v___x_723_ = v_s_515_;
v_isShared_724_ = v_isSharedCheck_887_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_children_721_);
lean_inc(v_element_720_);
lean_dec(v_s_515_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_887_;
goto v_resetjp_722_;
}
v___jp_519_:
{
lean_object* v___x_531_; double v___x_532_; double v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_531_ = lean_io_get_num_heartbeats();
v___x_532_ = lean_float_of_nat(v___y_526_);
v___x_533_ = lean_float_of_nat(v___x_531_);
v___x_534_ = lean_box_float(v___x_532_);
v___x_535_ = lean_box_float(v___x_533_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_530_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_525_);
v___x_538_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_525_, v___y_521_, v___y_524_, v___y_520_, v___y_523_, v___y_527_, v___y_522_, v___x_537_, v___y_529_, v___y_528_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_a_550_);
v___y_520_ = v___y_541_;
v___y_521_ = v___y_540_;
v___y_522_ = v___y_542_;
v___y_523_ = v___y_545_;
v___y_524_ = v___y_544_;
v___y_525_ = v___y_543_;
v___y_526_ = v___y_546_;
v___y_527_ = v___y_547_;
v___y_528_ = v___y_549_;
v___y_529_ = v___y_548_;
v_a_530_ = v___x_551_;
goto v___jp_519_;
}
v___jp_552_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v_a_563_);
v___y_520_ = v___y_554_;
v___y_521_ = v___y_553_;
v___y_522_ = v___y_555_;
v___y_523_ = v___y_558_;
v___y_524_ = v___y_557_;
v___y_525_ = v___y_556_;
v___y_526_ = v___y_559_;
v___y_527_ = v___y_560_;
v___y_528_ = v___y_562_;
v___y_529_ = v___y_561_;
v_a_530_ = v___x_564_;
goto v___jp_519_;
}
v___jp_565_:
{
if (lean_obj_tag(v___y_576_) == 0)
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v___y_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___y_576_, 1);
v___y_540_ = v___y_567_;
v___y_541_ = v___y_566_;
v___y_542_ = v___y_568_;
v___y_543_ = v___y_571_;
v___y_544_ = v___y_570_;
v___y_545_ = v___y_569_;
v___y_546_ = v___y_572_;
v___y_547_ = v___y_573_;
v___y_548_ = v___y_575_;
v___y_549_ = v___y_574_;
v_a_550_ = v_a_577_;
goto v___jp_539_;
}
else
{
lean_object* v_a_578_; 
v_a_578_ = lean_ctor_get(v___y_576_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___y_576_, 1);
v___y_553_ = v___y_567_;
v___y_554_ = v___y_566_;
v___y_555_ = v___y_568_;
v___y_556_ = v___y_571_;
v___y_557_ = v___y_570_;
v___y_558_ = v___y_569_;
v___y_559_ = v___y_572_;
v___y_560_ = v___y_573_;
v___y_561_ = v___y_575_;
v___y_562_ = v___y_574_;
v_a_563_ = v_a_578_;
goto v___jp_552_;
}
}
v___jp_579_:
{
lean_object* v___x_591_; double v___x_592_; double v___x_593_; double v___x_594_; double v___x_595_; double v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_591_ = lean_io_mono_nanos_now();
v___x_592_ = lean_float_of_nat(v___y_582_);
v___x_593_ = lean_float_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__0);
v___x_594_ = lean_float_div(v___x_592_, v___x_593_);
v___x_595_ = lean_float_of_nat(v___x_591_);
v___x_596_ = lean_float_div(v___x_595_, v___x_593_);
v___x_597_ = lean_box_float(v___x_594_);
v___x_598_ = lean_box_float(v___x_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_590_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_586_);
v___x_601_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6(v___y_586_, v___y_581_, v___y_585_, v___y_580_, v___y_584_, v___y_587_, v___y_583_, v___x_600_, v___y_589_, v___y_588_);
return v___x_601_;
}
v___jp_602_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_613_);
v___y_580_ = v___y_605_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_603_;
v___y_583_ = v___y_606_;
v___y_584_ = v___y_609_;
v___y_585_ = v___y_608_;
v___y_586_ = v___y_607_;
v___y_587_ = v___y_610_;
v___y_588_ = v___y_612_;
v___y_589_ = v___y_611_;
v_a_590_ = v___x_614_;
goto v___jp_579_;
}
v___jp_615_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_a_626_);
v___y_580_ = v___y_618_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_616_;
v___y_583_ = v___y_619_;
v___y_584_ = v___y_622_;
v___y_585_ = v___y_621_;
v___y_586_ = v___y_620_;
v___y_587_ = v___y_623_;
v___y_588_ = v___y_625_;
v___y_589_ = v___y_624_;
v_a_590_ = v___x_627_;
goto v___jp_579_;
}
v___jp_628_:
{
if (lean_obj_tag(v___y_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___y_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___y_639_, 1);
v___y_603_ = v___y_631_;
v___y_604_ = v___y_630_;
v___y_605_ = v___y_629_;
v___y_606_ = v___y_632_;
v___y_607_ = v___y_635_;
v___y_608_ = v___y_634_;
v___y_609_ = v___y_633_;
v___y_610_ = v___y_636_;
v___y_611_ = v___y_638_;
v___y_612_ = v___y_637_;
v_a_613_ = v_a_640_;
goto v___jp_602_;
}
else
{
lean_object* v_a_641_; 
v_a_641_ = lean_ctor_get(v___y_639_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___y_639_, 1);
v___y_616_ = v___y_631_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_629_;
v___y_619_ = v___y_632_;
v___y_620_ = v___y_635_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_633_;
v___y_623_ = v___y_636_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_637_;
v_a_626_ = v_a_641_;
goto v___jp_615_;
}
}
v___jp_642_:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__4___redArg(v___y_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_trace_profiler_useHeartbeats;
v___x_659_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v___y_647_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_io_mono_nanos_now();
v___x_661_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_649_, v___y_646_, v___y_655_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
if (lean_obj_tag(v___y_650_) == 1)
{
lean_object* v_val_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_val_662_ = lean_ctor_get(v___y_650_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___y_650_, 1);
v___x_663_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_644_);
v___x_664_ = l_Lean_Name_mkStr2(v___y_644_, v___x_663_);
v___x_665_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_664_);
v___x_666_ = l_Lean_Name_append(v___x_665_, v___x_664_);
v___x_667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_654_, v___y_647_, v___x_666_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v___x_664_);
lean_dec(v_val_662_);
v___x_668_ = lean_box(0);
v___y_603_ = v___x_660_;
v___y_604_ = v___y_643_;
v___y_605_ = v___y_647_;
v___y_606_ = v___y_648_;
v___y_607_ = v___y_652_;
v___y_608_ = v___y_651_;
v___y_609_ = v___y_645_;
v___y_610_ = v_a_657_;
v___y_611_ = v___y_646_;
v___y_612_ = v___y_655_;
v_a_613_ = v___x_668_;
goto v___jp_602_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_box(0);
v___x_670_ = l_Lean_Elab_InfoTree_format(v_val_662_, v___x_669_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_MessageData_ofFormat(v_a_671_);
v___x_673_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_664_, v___x_672_, v___y_646_, v___y_655_);
v___y_629_ = v___y_647_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_660_;
v___y_632_ = v___y_648_;
v___y_633_ = v___y_645_;
v___y_634_ = v___y_651_;
v___y_635_ = v___y_652_;
v___y_636_ = v_a_657_;
v___y_637_ = v___y_655_;
v___y_638_ = v___y_646_;
v___y_639_ = v___x_673_;
goto v___jp_628_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___x_664_);
v_a_674_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_684_ == 0)
{
v___x_676_ = v___x_670_;
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_io_error_to_string(v_a_674_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 3);
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_683_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lean_MessageData_ofFormat(v___x_680_);
lean_inc(v___y_653_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_653_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___y_616_ = v___x_660_;
v___y_617_ = v___y_643_;
v___y_618_ = v___y_647_;
v___y_619_ = v___y_648_;
v___y_620_ = v___y_652_;
v___y_621_ = v___y_651_;
v___y_622_ = v___y_645_;
v___y_623_ = v_a_657_;
v___y_624_ = v___y_646_;
v___y_625_ = v___y_655_;
v_a_626_ = v___x_682_;
goto v___jp_615_;
}
}
}
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v___y_650_);
v___x_685_ = lean_box(0);
v___y_603_ = v___x_660_;
v___y_604_ = v___y_643_;
v___y_605_ = v___y_647_;
v___y_606_ = v___y_648_;
v___y_607_ = v___y_652_;
v___y_608_ = v___y_651_;
v___y_609_ = v___y_645_;
v___y_610_ = v_a_657_;
v___y_611_ = v___y_646_;
v___y_612_ = v___y_655_;
v_a_613_ = v___x_685_;
goto v___jp_602_;
}
}
else
{
lean_dec(v___y_650_);
v___y_629_ = v___y_647_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_660_;
v___y_632_ = v___y_648_;
v___y_633_ = v___y_645_;
v___y_634_ = v___y_651_;
v___y_635_ = v___y_652_;
v___y_636_ = v_a_657_;
v___y_637_ = v___y_655_;
v___y_638_ = v___y_646_;
v___y_639_ = v___x_661_;
goto v___jp_628_;
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_io_get_num_heartbeats();
v___x_687_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___y_649_, v___y_646_, v___y_655_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref_known(v___x_687_, 1);
if (lean_obj_tag(v___y_650_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_val_688_ = lean_ctor_get(v___y_650_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___y_650_, 1);
v___x_689_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__1));
lean_inc_ref(v___y_644_);
v___x_690_ = l_Lean_Name_mkStr2(v___y_644_, v___x_689_);
v___x_691_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__3));
lean_inc(v___x_690_);
v___x_692_ = l_Lean_Name_append(v___x_691_, v___x_690_);
v___x_693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_654_, v___y_647_, v___x_692_);
lean_dec(v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v___x_690_);
lean_dec(v_val_688_);
v___x_694_ = lean_box(0);
v___y_540_ = v___y_643_;
v___y_541_ = v___y_647_;
v___y_542_ = v___y_648_;
v___y_543_ = v___y_652_;
v___y_544_ = v___y_651_;
v___y_545_ = v___y_645_;
v___y_546_ = v___x_686_;
v___y_547_ = v_a_657_;
v___y_548_ = v___y_646_;
v___y_549_ = v___y_655_;
v_a_550_ = v___x_694_;
goto v___jp_539_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Lean_Elab_InfoTree_format(v_val_688_, v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_MessageData_ofFormat(v_a_697_);
v___x_699_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_690_, v___x_698_, v___y_646_, v___y_655_);
v___y_566_ = v___y_647_;
v___y_567_ = v___y_643_;
v___y_568_ = v___y_648_;
v___y_569_ = v___y_645_;
v___y_570_ = v___y_651_;
v___y_571_ = v___y_652_;
v___y_572_ = v___x_686_;
v___y_573_ = v_a_657_;
v___y_574_ = v___y_655_;
v___y_575_ = v___y_646_;
v___y_576_ = v___x_699_;
goto v___jp_565_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___x_690_);
v_a_700_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v___x_696_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_io_error_to_string(v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 3);
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_709_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
lean_inc(v___y_653_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___y_653_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___y_553_ = v___y_643_;
v___y_554_ = v___y_647_;
v___y_555_ = v___y_648_;
v___y_556_ = v___y_652_;
v___y_557_ = v___y_651_;
v___y_558_ = v___y_645_;
v___y_559_ = v___x_686_;
v___y_560_ = v_a_657_;
v___y_561_ = v___y_646_;
v___y_562_ = v___y_655_;
v_a_563_ = v___x_708_;
goto v___jp_552_;
}
}
}
}
}
else
{
lean_object* v___x_711_; 
lean_dec(v___y_650_);
v___x_711_ = lean_box(0);
v___y_540_ = v___y_643_;
v___y_541_ = v___y_647_;
v___y_542_ = v___y_648_;
v___y_543_ = v___y_652_;
v___y_544_ = v___y_651_;
v___y_545_ = v___y_645_;
v___y_546_ = v___x_686_;
v___y_547_ = v_a_657_;
v___y_548_ = v___y_646_;
v___y_549_ = v___y_655_;
v_a_550_ = v___x_711_;
goto v___jp_539_;
}
}
else
{
lean_dec(v___y_650_);
v___y_566_ = v___y_647_;
v___y_567_ = v___y_643_;
v___y_568_ = v___y_648_;
v___y_569_ = v___y_645_;
v___y_570_ = v___y_651_;
v___y_571_ = v___y_652_;
v___y_572_ = v___x_686_;
v___y_573_ = v_a_657_;
v___y_574_ = v___y_655_;
v___y_575_ = v___y_646_;
v___y_576_ = v___x_687_;
goto v___jp_565_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
v_a_712_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_656_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_656_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
v_resetjp_722_:
{
lean_object* v_desc_725_; lean_object* v_diagnostics_726_; lean_object* v_infoTree_x3f_727_; lean_object* v_desc_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___x_822_; 
v_desc_725_ = lean_ctor_get(v_element_720_, 0);
lean_inc_ref(v_desc_725_);
v_diagnostics_726_ = lean_ctor_get(v_element_720_, 1);
lean_inc_ref(v_diagnostics_726_);
v_infoTree_x3f_727_ = lean_ctor_get(v_element_720_, 2);
lean_inc(v_infoTree_x3f_727_);
lean_dec_ref(v_element_720_);
v___x_822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_822_, 0, v_desc_725_);
switch(lean_obj_tag(v_range_x3f_514_))
{
case 0:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__13));
v___x_824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v_desc_729_ = v___x_824_;
v___y_730_ = v_a_516_;
v___y_731_ = v_a_517_;
goto v___jp_728_;
}
case 1:
{
lean_object* v_toCold_825_; lean_object* v_range_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_884_; 
v_toCold_825_ = lean_ctor_get(v_a_516_, 0);
v_range_826_ = lean_ctor_get(v_range_x3f_514_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_range_x3f_514_);
if (v_isSharedCheck_884_ == 0)
{
v___x_828_ = v_range_x3f_514_;
v_isShared_829_ = v_isSharedCheck_884_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_range_826_);
lean_dec(v_range_x3f_514_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_884_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_fileMap_830_; lean_object* v_start_831_; lean_object* v_stop_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_883_; 
v_fileMap_830_ = lean_ctor_get(v_toCold_825_, 1);
v_start_831_ = lean_ctor_get(v_range_826_, 0);
v_stop_832_ = lean_ctor_get(v_range_826_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_range_826_);
if (v_isSharedCheck_883_ == 0)
{
v___x_834_ = v_range_826_;
v_isShared_835_ = v_isSharedCheck_883_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_stop_832_);
lean_inc(v_start_831_);
lean_dec(v_range_826_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_883_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_line_837_; lean_object* v_column_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_882_; 
lean_inc_ref(v_fileMap_830_);
v___x_836_ = l_Lean_FileMap_toPosition(v_fileMap_830_, v_start_831_);
lean_dec(v_start_831_);
v_line_837_ = lean_ctor_get(v___x_836_, 0);
v_column_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_882_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_882_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_column_838_);
lean_inc(v_line_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_882_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v_line_843_; lean_object* v_column_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_881_; 
lean_inc_ref(v_fileMap_830_);
v___x_842_ = l_Lean_FileMap_toPosition(v_fileMap_830_, v_stop_832_);
lean_dec(v_stop_832_);
v_line_843_ = lean_ctor_get(v___x_842_, 0);
v_column_844_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_881_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_881_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_column_844_);
lean_inc(v_line_843_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_881_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__15));
v___x_849_ = l_Nat_reprFast(v_line_837_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 3);
lean_ctor_set(v___x_828_, 0, v___x_849_);
v___x_851_ = v___x_828_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_880_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 5);
lean_ctor_set(v___x_846_, 1, v___x_851_);
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_879_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__17));
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 5);
lean_ctor_set(v___x_840_, 1, v___x_854_);
lean_ctor_set(v___x_840_, 0, v___x_853_);
v___x_856_ = v___x_840_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_878_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = l_Nat_reprFast(v_column_838_);
v___x_858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 5);
lean_ctor_set(v___x_834_, 1, v___x_858_);
lean_ctor_set(v___x_834_, 0, v___x_856_);
v___x_860_ = v___x_834_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_877_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__19));
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__21));
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Nat_reprFast(v_line_843_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_848_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_854_);
v___x_869_ = l_Nat_reprFast(v_column_844_);
v___x_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_868_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_861_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_864_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__23));
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_822_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v_desc_729_ = v___x_876_;
v___y_730_ = v_a_516_;
v___y_731_ = v_a_517_;
goto v___jp_728_;
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
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__25));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_822_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v_desc_729_ = v___x_886_;
v___y_730_ = v_a_516_;
v___y_731_ = v_a_517_;
goto v___jp_728_;
}
}
v___jp_728_:
{
lean_object* v_msgLog_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_820_; 
v_msgLog_732_ = lean_ctor_get(v_diagnostics_726_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_diagnostics_726_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_diagnostics_726_, 1);
lean_dec(v_unused_821_);
v___x_734_ = v_diagnostics_726_;
v_isShared_735_ = v_isSharedCheck_820_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_msgLog_732_);
lean_dec(v_diagnostics_726_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_820_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_MessageLog_toList(v_msgLog_732_);
lean_dec_ref(v_msgLog_732_);
v___x_737_ = lean_box(0);
v___x_738_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v___x_736_, v___x_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_toCold_739_; lean_object* v_options_740_; lean_object* v_a_741_; lean_object* v_ref_742_; lean_object* v_inheritedTraceOptions_743_; uint8_t v_hasTrace_744_; lean_object* v___x_745_; 
v_toCold_739_ = lean_ctor_get(v___y_730_, 0);
v_options_740_ = lean_ctor_get(v_toCold_739_, 2);
v_a_741_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_738_, 1);
v_ref_742_ = lean_ctor_get(v___y_730_, 2);
v_inheritedTraceOptions_743_ = lean_ctor_get(v_toCold_739_, 11);
v_hasTrace_744_ = lean_ctor_get_uint8(v_options_740_, sizeof(void*)*1);
v___x_745_ = lean_array_to_list(v_children_721_);
if (v_hasTrace_744_ == 0)
{
lean_object* v___x_746_; 
lean_dec(v_a_741_);
lean_del_object(v___x_734_);
lean_dec(v_desc_729_);
lean_dec(v_infoTree_x3f_727_);
lean_del_object(v___x_723_);
v___x_746_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_745_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_755_);
v___x_748_ = v___x_746_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_746_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
return v___x_746_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__4));
v___x_757_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__6));
v___x_758_ = l_Std_Format_prefixJoin___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__3(v___x_757_, v_a_741_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 5);
lean_ctor_set(v___x_734_, 1, v___x_758_);
lean_ctor_set(v___x_734_, 0, v_desc_729_);
v___x_760_ = v___x_734_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_desc_729_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_811_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___f_761_ = lean_alloc_closure((void*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___lam__0___boxed), 5, 1);
lean_closure_set(v___f_761_, 0, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__8));
v___x_763_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2___closed__1));
v___x_764_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__9);
v___x_765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_743_, v_options_740_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = l_Lean_trace_profiler;
v___x_767_ = l_Lean_Option_get___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__5(v_options_740_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v___f_761_);
v___x_768_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v___x_745_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_809_; 
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_768_, 0);
lean_dec(v_unused_810_);
v___x_770_ = v___x_768_;
v_isShared_771_ = v_isSharedCheck_809_;
goto v_resetjp_769_;
}
else
{
lean_dec(v___x_768_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_809_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
if (lean_obj_tag(v_infoTree_x3f_727_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_804_; 
v_val_772_ = lean_ctor_get(v_infoTree_x3f_727_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_infoTree_x3f_727_);
if (v_isSharedCheck_804_ == 0)
{
v___x_774_ = v_infoTree_x3f_727_;
v_isShared_775_ = v_isSharedCheck_804_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v_infoTree_x3f_727_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_804_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__10));
v___x_777_ = lean_obj_once(&l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11, &l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11_once, _init_l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___closed__11);
v___x_778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_743_, v_options_740_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_del_object(v___x_774_);
lean_dec(v_val_772_);
lean_del_object(v___x_723_);
v___x_779_ = lean_box(0);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_779_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_770_);
v___x_783_ = lean_box(0);
v___x_784_ = l_Lean_Elab_InfoTree_format(v_val_772_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_del_object(v___x_774_);
lean_del_object(v___x_723_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = l_Lean_MessageData_ofFormat(v_a_785_);
v___x_787_ = l_Lean_addTrace___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__2(v___x_776_, v___x_786_, v___y_730_, v___y_731_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_803_; 
v_a_788_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_803_ == 0)
{
v___x_790_ = v___x_784_;
v_isShared_791_ = v_isSharedCheck_803_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_784_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_803_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_io_error_to_string(v_a_788_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 3);
lean_ctor_set(v___x_774_, 0, v___x_792_);
v___x_794_ = v___x_774_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_802_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_MessageData_ofFormat(v___x_794_);
lean_inc(v_ref_742_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_795_);
lean_ctor_set(v___x_723_, 0, v_ref_742_);
v___x_797_ = v___x_723_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_ref_742_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_801_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_797_);
v___x_799_ = v___x_790_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
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
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_infoTree_x3f_727_);
lean_del_object(v___x_723_);
v___x_805_ = lean_box(0);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_805_);
v___x_807_ = v___x_770_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_dec(v_infoTree_x3f_727_);
lean_del_object(v___x_723_);
return v___x_768_;
}
}
else
{
lean_del_object(v___x_723_);
v___y_643_ = v_hasTrace_744_;
v___y_644_ = v___x_756_;
v___y_645_ = v___x_765_;
v___y_646_ = v___y_730_;
v___y_647_ = v_options_740_;
v___y_648_ = v___f_761_;
v___y_649_ = v___x_745_;
v___y_650_ = v_infoTree_x3f_727_;
v___y_651_ = v___x_763_;
v___y_652_ = v___x_762_;
v___y_653_ = v_ref_742_;
v___y_654_ = v_inheritedTraceOptions_743_;
v___y_655_ = v___y_731_;
goto v___jp_642_;
}
}
else
{
lean_del_object(v___x_723_);
v___y_643_ = v_hasTrace_744_;
v___y_644_ = v___x_756_;
v___y_645_ = v___x_765_;
v___y_646_ = v___y_730_;
v___y_647_ = v_options_740_;
v___y_648_ = v___f_761_;
v___y_649_ = v___x_745_;
v___y_650_ = v_infoTree_x3f_727_;
v___y_651_ = v___x_763_;
v___y_652_ = v___x_762_;
v___y_653_ = v_ref_742_;
v___y_654_ = v_inheritedTraceOptions_743_;
v___y_655_ = v___y_731_;
goto v___jp_642_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_734_);
lean_dec(v_desc_729_);
lean_dec(v_infoTree_x3f_727_);
lean_del_object(v___x_723_);
lean_dec_ref(v_children_721_);
v_a_812_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_738_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_738_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(lean_object* v_as_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
if (lean_obj_tag(v_as_888_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v_reportingRange_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_head_894_ = lean_ctor_get(v_as_888_, 0);
lean_inc(v_head_894_);
v_tail_895_ = lean_ctor_get(v_as_888_, 1);
lean_inc(v_tail_895_);
lean_dec_ref_known(v_as_888_, 2);
v_reportingRange_896_ = lean_ctor_get(v_head_894_, 1);
lean_inc(v_reportingRange_896_);
v___x_897_ = l_Lean_Language_SnapshotTask_get___redArg(v_head_894_);
v___x_898_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_reportingRange_896_, v___x_897_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_dec_ref_known(v___x_898_, 1);
v_as_888_ = v_tail_895_;
goto _start;
}
else
{
lean_dec(v_tail_895_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1___boxed(lean_object* v_as_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_List_forM___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__1(v_as_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go___boxed(lean_object* v_range_x3f_905_, lean_object* v_s_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v_range_x3f_905_, v_s_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___redArg(v_x_911_, v_x_912_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0___boxed(lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_List_mapM_loop___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__0(v_x_917_, v_x_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(lean_object* v_00_u03b1_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___redArg(v_x_924_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9___boxed(lean_object* v_00_u03b1_929_, lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go_spec__6_spec__9(v_00_u03b1_929_, v_x_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace(lean_object* v_s_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_box(2);
v___x_940_ = l___private_Lean_Language_Util_0__Lean_Language_SnapshotTree_trace_go(v___x_939_, v_s_935_, v_a_936_, v_a_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_trace___boxed(lean_object* v_s_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Language_SnapshotTree_trace(v_s_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_945_;
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

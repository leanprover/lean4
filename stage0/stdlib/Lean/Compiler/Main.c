// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: public import Lean.Compiler.LCNF import Lean.Compiler.Options
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Compiler_LCNF_main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_compile___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "compiling: "};
static const lean_object* l_Lean_Compiler_compile___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_compile___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_compile___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Compiler_compile___lam__1___closed__0;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__1;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__2;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_compile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "compiler new"};
static const lean_object* l_Lean_Compiler_compile___closed__0 = (const lean_object*)&l_Lean_Compiler_compile___closed__0_value;
static const lean_string_object l_Lean_Compiler_compile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_compile___closed__1 = (const lean_object*)&l_Lean_Compiler_compile___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_compile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_compile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_object* l_Lean_Compiler_compile___closed__2 = (const lean_object*)&l_Lean_Compiler_compile___closed__2_value;
static const lean_string_object l_Lean_Compiler_compile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Compiler_compile___closed__3 = (const lean_object*)&l_Lean_Compiler_compile___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_compile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 231, 106, 210, 155, 191, 188, 215)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 110, 247, 202, 196, 18, 225, 12)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 199, 171, 242, 108, 0, 168, 62)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_compile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 224, 113, 12, 117, 229, 139, 207)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 173, 214, 72, 203, 43, 191, 75)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 211, 100, 122, 27, 185, 240, 172)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 110, 221, 45, 141, 179, 128, 62)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_compile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 7, 52, 191, 12, 227, 44, 166)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 220, 174, 246, 72, 178, 46, 181)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)(((size_t)(509999922) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(58, 199, 166, 135, 2, 243, 26, 150)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(21, 17, 12, 122, 46, 204, 68, 176)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 30, 97, 98, 87, 32, 148, 239)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 94, 102, 220, 218, 136, 156, 190)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stat"};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_compile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 239, 216, 162, 43, 249, 69, 56)}};
static const lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
lean_object* v_name_17_; lean_object* v_defValue_18_; lean_object* v_map_19_; lean_object* v___x_20_; 
v_name_17_ = lean_ctor_get(v_opt_16_, 0);
v_defValue_18_ = lean_ctor_get(v_opt_16_, 1);
v_map_19_ = lean_ctor_get(v_opts_15_, 0);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_19_, v_name_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
else
{
lean_object* v_val_21_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref(v___x_20_);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref(v_val_21_);
return v_v_22_;
}
else
{
lean_dec(v_val_21_);
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object* v_opts_23_, lean_object* v_opt_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_23_, v_opt_24_);
lean_dec_ref(v_opt_24_);
lean_dec_ref(v_opts_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg(lean_object* v_cls_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_options_32_; uint8_t v_hasTrace_33_; 
v_options_32_ = lean_ctor_get(v___y_30_, 2);
v_hasTrace_33_ = lean_ctor_get_uint8(v_options_32_, sizeof(void*)*1);
if (v_hasTrace_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_cls_29_);
v___x_34_ = lean_box(v_hasTrace_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_inheritedTraceOptions_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_inheritedTraceOptions_36_ = lean_ctor_get(v___y_30_, 13);
v___x_37_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__1));
v___x_38_ = l_Lean_Name_append(v___x_37_, v_cls_29_);
v___x_39_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_36_, v_options_32_, v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lean_box(v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___boxed(lean_object* v_cls_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg(v_cls_42_, v___y_43_);
lean_dec_ref(v___y_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg(v_cls_46_, v___y_47_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4(v_cls_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_55_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_unsigned_to_nat(32u);
v___x_57_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_59_ = ((size_t)5ULL);
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_unsigned_to_nat(32u);
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_61_);
v___x_63_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__0);
v___x_64_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_60_);
lean_ctor_set(v___x_64_, 3, v___x_60_);
lean_ctor_set_usize(v___x_64_, 4, v___x_59_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg(lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_traceState_68_; lean_object* v_traces_69_; lean_object* v___x_70_; lean_object* v_traceState_71_; lean_object* v_env_72_; lean_object* v_nextMacroScope_73_; lean_object* v_ngen_74_; lean_object* v_auxDeclNGen_75_; lean_object* v_cache_76_; lean_object* v_messages_77_; lean_object* v_infoState_78_; lean_object* v_snapshotTasks_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_98_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_traceState_68_ = lean_ctor_get(v___x_67_, 4);
lean_inc_ref(v_traceState_68_);
lean_dec(v___x_67_);
v_traces_69_ = lean_ctor_get(v_traceState_68_, 0);
lean_inc_ref(v_traces_69_);
lean_dec_ref(v_traceState_68_);
v___x_70_ = lean_st_ref_take(v___y_65_);
v_traceState_71_ = lean_ctor_get(v___x_70_, 4);
v_env_72_ = lean_ctor_get(v___x_70_, 0);
v_nextMacroScope_73_ = lean_ctor_get(v___x_70_, 1);
v_ngen_74_ = lean_ctor_get(v___x_70_, 2);
v_auxDeclNGen_75_ = lean_ctor_get(v___x_70_, 3);
v_cache_76_ = lean_ctor_get(v___x_70_, 5);
v_messages_77_ = lean_ctor_get(v___x_70_, 6);
v_infoState_78_ = lean_ctor_get(v___x_70_, 7);
v_snapshotTasks_79_ = lean_ctor_get(v___x_70_, 8);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_98_ == 0)
{
v___x_81_ = v___x_70_;
v_isShared_82_ = v_isSharedCheck_98_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_snapshotTasks_79_);
lean_inc(v_infoState_78_);
lean_inc(v_messages_77_);
lean_inc(v_cache_76_);
lean_inc(v_traceState_71_);
lean_inc(v_auxDeclNGen_75_);
lean_inc(v_ngen_74_);
lean_inc(v_nextMacroScope_73_);
lean_inc(v_env_72_);
lean_dec(v___x_70_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_98_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint64_t v_tid_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_tid_83_ = lean_ctor_get_uint64(v_traceState_71_, sizeof(void*)*1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_traceState_71_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_traceState_71_, 0);
lean_dec(v_unused_97_);
v___x_85_ = v_traceState_71_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_dec(v_traceState_71_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___closed__1);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_87_);
lean_ctor_set_uint64(v_reuseFailAlloc_95_, sizeof(void*)*1, v_tid_83_);
v___x_89_ = v_reuseFailAlloc_95_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 4, v___x_89_);
v___x_91_ = v___x_81_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_env_72_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_nextMacroScope_73_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_ngen_74_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_auxDeclNGen_75_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_94_, 5, v_cache_76_);
lean_ctor_set(v_reuseFailAlloc_94_, 6, v_messages_77_);
lean_ctor_set(v_reuseFailAlloc_94_, 7, v_infoState_78_);
lean_ctor_set(v_reuseFailAlloc_94_, 8, v_snapshotTasks_79_);
v___x_91_ = v_reuseFailAlloc_94_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_st_ref_set(v___y_65_, v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_traces_69_);
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg___boxed(lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg(v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg(v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5(v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg(lean_object* v_category_110_, lean_object* v_opts_111_, lean_object* v_act_112_, lean_object* v_decl_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
v___x_117_ = lean_apply_2(v_act_112_, v___y_114_, v___y_115_);
v___x_118_ = l_Lean_profileitIOUnsafe___redArg(v_category_110_, v_opts_111_, v___x_117_, v_decl_113_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg___boxed(lean_object* v_category_119_, lean_object* v_opts_120_, lean_object* v_act_121_, lean_object* v_decl_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg(v_category_119_, v_opts_120_, v_act_121_, v_decl_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec_ref(v_opts_120_);
lean_dec_ref(v_category_119_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7(lean_object* v_00_u03b1_127_, lean_object* v_category_128_, lean_object* v_opts_129_, lean_object* v_act_130_, lean_object* v_decl_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg(v_category_128_, v_opts_129_, v_act_130_, v_decl_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___boxed(lean_object* v_00_u03b1_136_, lean_object* v_category_137_, lean_object* v_opts_138_, lean_object* v_act_139_, lean_object* v_decl_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7(v_00_u03b1_136_, v_category_137_, v_opts_138_, v_act_139_, v_decl_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec_ref(v_opts_138_);
lean_dec_ref(v_category_137_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
if (lean_obj_tag(v_a_145_) == 0)
{
lean_object* v___x_147_; 
v___x_147_ = l_List_reverse___redArg(v_a_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_158_; 
v_head_148_ = lean_ctor_get(v_a_145_, 0);
v_tail_149_ = lean_ctor_get(v_a_145_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_158_ == 0)
{
v___x_151_ = v_a_145_;
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_tail_149_);
lean_inc(v_head_148_);
lean_dec(v_a_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = l_Lean_MessageData_ofName(v_head_148_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_a_146_);
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_146_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v_a_145_ = v_tail_149_;
v_a_146_ = v___x_155_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Compiler_compile___lam__0___closed__0));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object* v_declNames_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_167_ = lean_obj_once(&l_Lean_Compiler_compile___lam__0___closed__1, &l_Lean_Compiler_compile___lam__0___closed__1_once, _init_l_Lean_Compiler_compile___lam__0___closed__1);
v___x_168_ = lean_array_to_list(v_declNames_162_);
v___x_169_ = lean_box(0);
v___x_170_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_168_, v___x_169_);
v___x_171_ = l_Lean_MessageData_ofList(v___x_170_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_167_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* v_declNames_174_, lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Compiler_compile___lam__0(v_declNames_174_, v_x_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec_ref(v_x_175_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(lean_object* v_o_180_, lean_object* v_k_181_, uint8_t v_v_182_){
_start:
{
lean_object* v_map_183_; uint8_t v_hasTrace_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_198_; 
v_map_183_ = lean_ctor_get(v_o_180_, 0);
v_hasTrace_184_ = lean_ctor_get_uint8(v_o_180_, sizeof(void*)*1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_o_180_);
if (v_isSharedCheck_198_ == 0)
{
v___x_186_ = v_o_180_;
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_map_183_);
lean_dec(v_o_180_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_188_, 0, v_v_182_);
lean_inc(v_k_181_);
v___x_189_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_181_, v___x_188_, v_map_183_);
if (v_hasTrace_184_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_193_; 
v___x_190_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg___closed__1));
v___x_191_ = l_Lean_Name_isPrefixOf(v___x_190_, v_k_181_);
lean_dec(v_k_181_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_189_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_191_);
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v_k_181_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_196_ = v___x_186_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*1, v_hasTrace_184_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(lean_object* v_o_199_, lean_object* v_k_200_, lean_object* v_v_201_){
_start:
{
uint8_t v_v_boxed_202_; lean_object* v_res_203_; 
v_v_boxed_202_ = lean_unbox(v_v_201_);
v_res_203_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_o_199_, v_k_200_, v_v_boxed_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(lean_object* v_opts_204_, lean_object* v_opt_205_, uint8_t v_val_206_){
_start:
{
lean_object* v_name_207_; lean_object* v___x_208_; 
v_name_207_ = lean_ctor_get(v_opt_205_, 0);
lean_inc(v_name_207_);
lean_dec_ref(v_opt_205_);
v___x_208_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_opts_204_, v_name_207_, v_val_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(lean_object* v_opts_209_, lean_object* v_opt_210_, lean_object* v_val_211_){
_start:
{
uint8_t v_val_boxed_212_; lean_object* v_res_213_; 
v_val_boxed_212_ = lean_unbox(v_val_211_);
v_res_213_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_opts_209_, v_opt_210_, v_val_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v_x_214_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v_x_214_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v_x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v_x_214_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v_x_214_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v_x_214_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 0);
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg___boxed(lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7(lean_object* v_e_235_){
_start:
{
if (lean_obj_tag(v_e_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = 2;
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7___boxed(lean_object* v_e_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7(v_e_238_);
lean_dec_ref(v_e_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
lean_ctor_set(v___x_246_, 3, v___x_244_);
lean_ctor_set(v___x_246_, 4, v___x_244_);
lean_ctor_set(v___x_246_, 5, v___x_244_);
lean_ctor_set(v___x_246_, 6, v___x_244_);
lean_ctor_set(v___x_246_, 7, v___x_244_);
lean_ctor_set(v___x_246_, 8, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(32u);
v___x_248_ = lean_mk_empty_array_with_capacity(v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4(void){
_start:
{
size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_250_ = ((size_t)5ULL);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_unsigned_to_nat(32u);
v___x_253_ = lean_mk_empty_array_with_capacity(v___x_252_);
v___x_254_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__3);
v___x_255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_251_);
lean_ctor_set(v___x_255_, 3, v___x_251_);
lean_ctor_set_usize(v___x_255_, 4, v___x_250_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_256_ = lean_box(1);
v___x_257_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__4);
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__1);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; lean_object* v_env_265_; lean_object* v_options_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_264_ = lean_st_ref_get(v___y_262_);
v_env_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc_ref(v_env_265_);
lean_dec(v___x_264_);
v_options_266_ = lean_ctor_get(v___y_261_, 2);
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__2);
v___x_268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___closed__5);
lean_inc_ref(v_options_266_);
v___x_269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_269_, 0, v_env_265_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
lean_ctor_set(v___x_269_, 3, v_options_266_);
v___x_270_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_msgData_260_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11___boxed(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11(v_msgData_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10(size_t v_sz_277_, size_t v_i_278_, lean_object* v_bs_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_lt(v_i_278_, v_sz_277_);
if (v___x_280_ == 0)
{
return v_bs_279_;
}
else
{
lean_object* v_v_281_; lean_object* v_msg_282_; lean_object* v___x_283_; lean_object* v_bs_x27_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_v_281_ = lean_array_uget_borrowed(v_bs_279_, v_i_278_);
v_msg_282_ = lean_ctor_get(v_v_281_, 1);
lean_inc_ref(v_msg_282_);
v___x_283_ = lean_unsigned_to_nat(0u);
v_bs_x27_284_ = lean_array_uset(v_bs_279_, v_i_278_, v___x_283_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_278_, v___x_285_);
v___x_287_ = lean_array_uset(v_bs_x27_284_, v_i_278_, v_msg_282_);
v_i_278_ = v___x_286_;
v_bs_279_ = v___x_287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10___boxed(lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_bs_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_293_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10(v_sz_boxed_292_, v_i_boxed_293_, v_bs_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8(lean_object* v_oldTraces_295_, lean_object* v_data_296_, lean_object* v_ref_297_, lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_fileName_302_; lean_object* v_fileMap_303_; lean_object* v_options_304_; lean_object* v_currRecDepth_305_; lean_object* v_maxRecDepth_306_; lean_object* v_ref_307_; lean_object* v_currNamespace_308_; lean_object* v_openDecls_309_; lean_object* v_initHeartbeats_310_; lean_object* v_maxHeartbeats_311_; lean_object* v_quotContext_312_; lean_object* v_currMacroScope_313_; uint8_t v_diag_314_; lean_object* v_cancelTk_x3f_315_; uint8_t v_suppressElabErrors_316_; lean_object* v_inheritedTraceOptions_317_; lean_object* v___x_318_; lean_object* v_traceState_319_; lean_object* v_traces_320_; lean_object* v_ref_321_; lean_object* v___x_322_; lean_object* v___x_323_; size_t v_sz_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v_msg_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_366_; 
v_fileName_302_ = lean_ctor_get(v___y_299_, 0);
v_fileMap_303_ = lean_ctor_get(v___y_299_, 1);
v_options_304_ = lean_ctor_get(v___y_299_, 2);
v_currRecDepth_305_ = lean_ctor_get(v___y_299_, 3);
v_maxRecDepth_306_ = lean_ctor_get(v___y_299_, 4);
v_ref_307_ = lean_ctor_get(v___y_299_, 5);
v_currNamespace_308_ = lean_ctor_get(v___y_299_, 6);
v_openDecls_309_ = lean_ctor_get(v___y_299_, 7);
v_initHeartbeats_310_ = lean_ctor_get(v___y_299_, 8);
v_maxHeartbeats_311_ = lean_ctor_get(v___y_299_, 9);
v_quotContext_312_ = lean_ctor_get(v___y_299_, 10);
v_currMacroScope_313_ = lean_ctor_get(v___y_299_, 11);
v_diag_314_ = lean_ctor_get_uint8(v___y_299_, sizeof(void*)*14);
v_cancelTk_x3f_315_ = lean_ctor_get(v___y_299_, 12);
v_suppressElabErrors_316_ = lean_ctor_get_uint8(v___y_299_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_317_ = lean_ctor_get(v___y_299_, 13);
v___x_318_ = lean_st_ref_get(v___y_300_);
v_traceState_319_ = lean_ctor_get(v___x_318_, 4);
lean_inc_ref(v_traceState_319_);
lean_dec(v___x_318_);
v_traces_320_ = lean_ctor_get(v_traceState_319_, 0);
lean_inc_ref(v_traces_320_);
lean_dec_ref(v_traceState_319_);
v_ref_321_ = l_Lean_replaceRef(v_ref_297_, v_ref_307_);
lean_inc_ref(v_inheritedTraceOptions_317_);
lean_inc(v_cancelTk_x3f_315_);
lean_inc(v_currMacroScope_313_);
lean_inc(v_quotContext_312_);
lean_inc(v_maxHeartbeats_311_);
lean_inc(v_initHeartbeats_310_);
lean_inc(v_openDecls_309_);
lean_inc(v_currNamespace_308_);
lean_inc(v_maxRecDepth_306_);
lean_inc(v_currRecDepth_305_);
lean_inc_ref(v_options_304_);
lean_inc_ref(v_fileMap_303_);
lean_inc_ref(v_fileName_302_);
v___x_322_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_322_, 0, v_fileName_302_);
lean_ctor_set(v___x_322_, 1, v_fileMap_303_);
lean_ctor_set(v___x_322_, 2, v_options_304_);
lean_ctor_set(v___x_322_, 3, v_currRecDepth_305_);
lean_ctor_set(v___x_322_, 4, v_maxRecDepth_306_);
lean_ctor_set(v___x_322_, 5, v_ref_321_);
lean_ctor_set(v___x_322_, 6, v_currNamespace_308_);
lean_ctor_set(v___x_322_, 7, v_openDecls_309_);
lean_ctor_set(v___x_322_, 8, v_initHeartbeats_310_);
lean_ctor_set(v___x_322_, 9, v_maxHeartbeats_311_);
lean_ctor_set(v___x_322_, 10, v_quotContext_312_);
lean_ctor_set(v___x_322_, 11, v_currMacroScope_313_);
lean_ctor_set(v___x_322_, 12, v_cancelTk_x3f_315_);
lean_ctor_set(v___x_322_, 13, v_inheritedTraceOptions_317_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*14, v_diag_314_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*14 + 1, v_suppressElabErrors_316_);
v___x_323_ = l_Lean_PersistentArray_toArray___redArg(v_traces_320_);
lean_dec_ref(v_traces_320_);
v_sz_324_ = lean_array_size(v___x_323_);
v___x_325_ = ((size_t)0ULL);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__10(v_sz_324_, v___x_325_, v___x_323_);
v_msg_327_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_327_, 0, v_data_296_);
lean_ctor_set(v_msg_327_, 1, v_msg_298_);
lean_ctor_set(v_msg_327_, 2, v___x_326_);
v___x_328_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8_spec__11(v_msg_327_, v___x_322_, v___y_300_);
lean_dec_ref(v___x_322_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_366_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_366_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_366_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v_traceState_334_; lean_object* v_env_335_; lean_object* v_nextMacroScope_336_; lean_object* v_ngen_337_; lean_object* v_auxDeclNGen_338_; lean_object* v_cache_339_; lean_object* v_messages_340_; lean_object* v_infoState_341_; lean_object* v_snapshotTasks_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_365_; 
v___x_333_ = lean_st_ref_take(v___y_300_);
v_traceState_334_ = lean_ctor_get(v___x_333_, 4);
v_env_335_ = lean_ctor_get(v___x_333_, 0);
v_nextMacroScope_336_ = lean_ctor_get(v___x_333_, 1);
v_ngen_337_ = lean_ctor_get(v___x_333_, 2);
v_auxDeclNGen_338_ = lean_ctor_get(v___x_333_, 3);
v_cache_339_ = lean_ctor_get(v___x_333_, 5);
v_messages_340_ = lean_ctor_get(v___x_333_, 6);
v_infoState_341_ = lean_ctor_get(v___x_333_, 7);
v_snapshotTasks_342_ = lean_ctor_get(v___x_333_, 8);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_365_ == 0)
{
v___x_344_ = v___x_333_;
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snapshotTasks_342_);
lean_inc(v_infoState_341_);
lean_inc(v_messages_340_);
lean_inc(v_cache_339_);
lean_inc(v_traceState_334_);
lean_inc(v_auxDeclNGen_338_);
lean_inc(v_ngen_337_);
lean_inc(v_nextMacroScope_336_);
lean_inc(v_env_335_);
lean_dec(v___x_333_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint64_t v_tid_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_363_; 
v_tid_346_ = lean_ctor_get_uint64(v_traceState_334_, sizeof(void*)*1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_traceState_334_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v_traceState_334_, 0);
lean_dec(v_unused_364_);
v___x_348_ = v_traceState_334_;
v_isShared_349_ = v_isSharedCheck_363_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_traceState_334_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_363_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_ref_297_);
lean_ctor_set(v___x_350_, 1, v_a_329_);
v___x_351_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_295_, v___x_350_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_351_);
lean_ctor_set_uint64(v_reuseFailAlloc_362_, sizeof(void*)*1, v_tid_346_);
v___x_353_ = v_reuseFailAlloc_362_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v___x_353_);
v___x_355_ = v___x_344_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_env_335_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_nextMacroScope_336_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_ngen_337_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_auxDeclNGen_338_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_cache_339_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_messages_340_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v_infoState_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_snapshotTasks_342_);
v___x_355_ = v_reuseFailAlloc_361_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_356_ = lean_st_ref_set(v___y_300_, v___x_355_);
v___x_357_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_357_);
v___x_359_ = v___x_331_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8___boxed(lean_object* v_oldTraces_367_, lean_object* v_data_368_, lean_object* v_ref_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8(v_oldTraces_367_, v_data_368_, v_ref_369_, v_msg_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_374_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__0));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2(void){
_start:
{
lean_object* v___x_378_; double v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_float_of_nat(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__3));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5(void){
_start:
{
lean_object* v___x_383_; double v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(1000u);
v___x_384_ = lean_float_of_nat(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6(lean_object* v_cls_385_, uint8_t v_collapsed_386_, lean_object* v_tag_387_, lean_object* v_opts_388_, uint8_t v_clsEnabled_389_, lean_object* v_oldTraces_390_, lean_object* v_msg_391_, lean_object* v_resStartStop_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_487_; 
v_fst_396_ = lean_ctor_get(v_resStartStop_392_, 0);
v_snd_397_ = lean_ctor_get(v_resStartStop_392_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_resStartStop_392_);
if (v_isSharedCheck_487_ == 0)
{
v___x_399_ = v_resStartStop_392_;
v_isShared_400_ = v_isSharedCheck_487_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_resStartStop_392_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_487_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v_data_404_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_486_; 
v_fst_407_ = lean_ctor_get(v_snd_397_, 0);
v_snd_408_ = lean_ctor_get(v_snd_397_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_snd_397_);
if (v_isSharedCheck_486_ == 0)
{
v___x_410_ = v_snd_397_;
v_isShared_411_ = v_isSharedCheck_486_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
lean_dec(v_snd_397_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_486_;
goto v_resetjp_409_;
}
v___jp_401_:
{
lean_object* v___x_405_; 
lean_inc(v___y_402_);
v___x_405_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__8(v_oldTraces_390_, v_data_404_, v___y_402_, v___y_403_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_405_);
v___x_406_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(v_fst_396_);
return v___x_406_;
}
else
{
lean_dec(v_fst_396_);
return v___x_405_;
}
}
v_resetjp_409_:
{
lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___y_415_; lean_object* v_a_416_; uint8_t v___y_440_; double v___y_471_; 
v___x_412_ = l_Lean_trace_profiler;
v___x_413_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_388_, v___x_412_);
if (v___x_413_ == 0)
{
v___y_440_ = v___x_413_;
goto v___jp_439_;
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = l_Lean_trace_profiler_useHeartbeats;
v___x_477_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_388_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; double v___x_480_; double v___x_481_; double v___x_482_; 
v___x_478_ = l_Lean_trace_profiler_threshold;
v___x_479_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_388_, v___x_478_);
v___x_480_ = lean_float_of_nat(v___x_479_);
v___x_481_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__5);
v___x_482_ = lean_float_div(v___x_480_, v___x_481_);
v___y_471_ = v___x_482_;
goto v___jp_470_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; double v___x_485_; 
v___x_483_ = l_Lean_trace_profiler_threshold;
v___x_484_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_388_, v___x_483_);
v___x_485_ = lean_float_of_nat(v___x_484_);
v___y_471_ = v___x_485_;
goto v___jp_470_;
}
}
v___jp_414_:
{
uint8_t v_result_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v_result_417_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__7(v_fst_396_);
v___x_418_ = l_Lean_TraceResult_toEmoji(v_result_417_);
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
v___x_420_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__1);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 7);
lean_ctor_set(v___x_410_, 1, v___x_420_);
lean_ctor_set(v___x_410_, 0, v___x_419_);
v___x_422_ = v___x_410_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_433_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v_m_424_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 7);
lean_ctor_set(v___x_399_, 1, v_a_416_);
lean_ctor_set(v___x_399_, 0, v___x_422_);
v_m_424_ = v___x_399_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_416_);
v_m_424_ = v_reuseFailAlloc_432_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; double v___x_427_; lean_object* v_data_428_; 
v___x_425_ = lean_box(v_result_417_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
v___x_427_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__2);
lean_inc_ref(v_tag_387_);
lean_inc_ref(v___x_426_);
lean_inc(v_cls_385_);
v_data_428_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_428_, 0, v_cls_385_);
lean_ctor_set(v_data_428_, 1, v___x_426_);
lean_ctor_set(v_data_428_, 2, v_tag_387_);
lean_ctor_set_float(v_data_428_, sizeof(void*)*3, v___x_427_);
lean_ctor_set_float(v_data_428_, sizeof(void*)*3 + 8, v___x_427_);
lean_ctor_set_uint8(v_data_428_, sizeof(void*)*3 + 16, v_collapsed_386_);
if (v___x_413_ == 0)
{
lean_dec_ref(v___x_426_);
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_dec_ref(v_tag_387_);
lean_dec(v_cls_385_);
v___y_402_ = v___y_415_;
v___y_403_ = v_m_424_;
v_data_404_ = v_data_428_;
goto v___jp_401_;
}
else
{
lean_object* v_data_429_; double v___x_430_; double v___x_431_; 
lean_dec_ref(v_data_428_);
v_data_429_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_429_, 0, v_cls_385_);
lean_ctor_set(v_data_429_, 1, v___x_426_);
lean_ctor_set(v_data_429_, 2, v_tag_387_);
v___x_430_ = lean_unbox_float(v_fst_407_);
lean_dec(v_fst_407_);
lean_ctor_set_float(v_data_429_, sizeof(void*)*3, v___x_430_);
v___x_431_ = lean_unbox_float(v_snd_408_);
lean_dec(v_snd_408_);
lean_ctor_set_float(v_data_429_, sizeof(void*)*3 + 8, v___x_431_);
lean_ctor_set_uint8(v_data_429_, sizeof(void*)*3 + 16, v_collapsed_386_);
v___y_402_ = v___y_415_;
v___y_403_ = v_m_424_;
v_data_404_ = v_data_429_;
goto v___jp_401_;
}
}
}
}
v___jp_434_:
{
lean_object* v_ref_435_; lean_object* v___x_436_; 
v_ref_435_ = lean_ctor_get(v___y_393_, 5);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v_fst_396_);
v___x_436_ = lean_apply_4(v_msg_391_, v_fst_396_, v___y_393_, v___y_394_, lean_box(0));
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v___y_415_ = v_ref_435_;
v_a_416_ = v_a_437_;
goto v___jp_414_;
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v___x_436_);
v___x_438_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___closed__4);
v___y_415_ = v_ref_435_;
v_a_416_ = v___x_438_;
goto v___jp_414_;
}
}
v___jp_439_:
{
if (v_clsEnabled_389_ == 0)
{
if (v___y_440_ == 0)
{
lean_object* v___x_441_; lean_object* v_traceState_442_; lean_object* v_env_443_; lean_object* v_nextMacroScope_444_; lean_object* v_ngen_445_; lean_object* v_auxDeclNGen_446_; lean_object* v_cache_447_; lean_object* v_messages_448_; lean_object* v_infoState_449_; lean_object* v_snapshotTasks_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_469_; 
lean_del_object(v___x_410_);
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_del_object(v___x_399_);
lean_dec_ref(v_msg_391_);
lean_dec_ref(v_tag_387_);
lean_dec(v_cls_385_);
v___x_441_ = lean_st_ref_take(v___y_394_);
v_traceState_442_ = lean_ctor_get(v___x_441_, 4);
v_env_443_ = lean_ctor_get(v___x_441_, 0);
v_nextMacroScope_444_ = lean_ctor_get(v___x_441_, 1);
v_ngen_445_ = lean_ctor_get(v___x_441_, 2);
v_auxDeclNGen_446_ = lean_ctor_get(v___x_441_, 3);
v_cache_447_ = lean_ctor_get(v___x_441_, 5);
v_messages_448_ = lean_ctor_get(v___x_441_, 6);
v_infoState_449_ = lean_ctor_get(v___x_441_, 7);
v_snapshotTasks_450_ = lean_ctor_get(v___x_441_, 8);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_469_ == 0)
{
v___x_452_ = v___x_441_;
v_isShared_453_ = v_isSharedCheck_469_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snapshotTasks_450_);
lean_inc(v_infoState_449_);
lean_inc(v_messages_448_);
lean_inc(v_cache_447_);
lean_inc(v_traceState_442_);
lean_inc(v_auxDeclNGen_446_);
lean_inc(v_ngen_445_);
lean_inc(v_nextMacroScope_444_);
lean_inc(v_env_443_);
lean_dec(v___x_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_469_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint64_t v_tid_454_; lean_object* v_traces_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_468_; 
v_tid_454_ = lean_ctor_get_uint64(v_traceState_442_, sizeof(void*)*1);
v_traces_455_ = lean_ctor_get(v_traceState_442_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_traceState_442_);
if (v_isSharedCheck_468_ == 0)
{
v___x_457_ = v_traceState_442_;
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_traces_455_);
lean_dec(v_traceState_442_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_390_, v_traces_455_);
lean_dec_ref(v_traces_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_459_);
lean_ctor_set_uint64(v_reuseFailAlloc_467_, sizeof(void*)*1, v_tid_454_);
v___x_461_ = v_reuseFailAlloc_467_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v___x_461_);
v___x_463_ = v___x_452_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_env_443_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_nextMacroScope_444_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_ngen_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_auxDeclNGen_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_cache_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_messages_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_infoState_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_snapshotTasks_450_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_st_ref_set(v___y_394_, v___x_463_);
v___x_465_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(v_fst_396_);
return v___x_465_;
}
}
}
}
}
else
{
goto v___jp_434_;
}
}
else
{
goto v___jp_434_;
}
}
v___jp_470_:
{
double v___x_472_; double v___x_473_; double v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_unbox_float(v_snd_408_);
v___x_473_ = lean_unbox_float(v_fst_407_);
v___x_474_ = lean_float_sub(v___x_472_, v___x_473_);
v___x_475_ = lean_float_decLt(v___y_471_, v___x_474_);
v___y_440_ = v___x_475_;
goto v___jp_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6___boxed(lean_object* v_cls_488_, lean_object* v_collapsed_489_, lean_object* v_tag_490_, lean_object* v_opts_491_, lean_object* v_clsEnabled_492_, lean_object* v_oldTraces_493_, lean_object* v_msg_494_, lean_object* v_resStartStop_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v_collapsed_boxed_499_; uint8_t v_clsEnabled_boxed_500_; lean_object* v_res_501_; 
v_collapsed_boxed_499_ = lean_unbox(v_collapsed_489_);
v_clsEnabled_boxed_500_ = lean_unbox(v_clsEnabled_492_);
v_res_501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6(v_cls_488_, v_collapsed_boxed_499_, v_tag_490_, v_opts_491_, v_clsEnabled_boxed_500_, v_oldTraces_493_, v_msg_494_, v_resStartStop_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec_ref(v_opts_491_);
return v_res_501_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_502_; double v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1000000000u);
v___x_503_ = lean_float_of_nat(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__3(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_509_, uint8_t v___x_510_, lean_object* v___x_511_, lean_object* v___f_512_, lean_object* v_declNames_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_fileName_518_; lean_object* v_fileMap_519_; lean_object* v_options_520_; lean_object* v_currRecDepth_521_; lean_object* v_ref_522_; lean_object* v_currNamespace_523_; lean_object* v_openDecls_524_; lean_object* v_initHeartbeats_525_; lean_object* v_maxHeartbeats_526_; lean_object* v_quotContext_527_; lean_object* v_currMacroScope_528_; lean_object* v_cancelTk_x3f_529_; uint8_t v_suppressElabErrors_530_; lean_object* v_inheritedTraceOptions_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_671_; 
v___x_517_ = lean_st_ref_get(v___y_515_);
v_fileName_518_ = lean_ctor_get(v___y_514_, 0);
v_fileMap_519_ = lean_ctor_get(v___y_514_, 1);
v_options_520_ = lean_ctor_get(v___y_514_, 2);
v_currRecDepth_521_ = lean_ctor_get(v___y_514_, 3);
v_ref_522_ = lean_ctor_get(v___y_514_, 5);
v_currNamespace_523_ = lean_ctor_get(v___y_514_, 6);
v_openDecls_524_ = lean_ctor_get(v___y_514_, 7);
v_initHeartbeats_525_ = lean_ctor_get(v___y_514_, 8);
v_maxHeartbeats_526_ = lean_ctor_get(v___y_514_, 9);
v_quotContext_527_ = lean_ctor_get(v___y_514_, 10);
v_currMacroScope_528_ = lean_ctor_get(v___y_514_, 11);
v_cancelTk_x3f_529_ = lean_ctor_get(v___y_514_, 12);
v_suppressElabErrors_530_ = lean_ctor_get_uint8(v___y_514_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_531_ = lean_ctor_get(v___y_514_, 13);
v_isSharedCheck_671_ = !lean_is_exclusive(v___y_514_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___y_514_, 4);
lean_dec(v_unused_672_);
v___x_533_ = v___y_514_;
v_isShared_534_ = v_isSharedCheck_671_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_inheritedTraceOptions_531_);
lean_inc(v_cancelTk_x3f_529_);
lean_inc(v_currMacroScope_528_);
lean_inc(v_quotContext_527_);
lean_inc(v_maxHeartbeats_526_);
lean_inc(v_initHeartbeats_525_);
lean_inc(v_openDecls_524_);
lean_inc(v_currNamespace_523_);
lean_inc(v_ref_522_);
lean_inc(v_currRecDepth_521_);
lean_inc(v_options_520_);
lean_inc(v_fileMap_519_);
lean_inc(v_fileName_518_);
lean_dec(v___y_514_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_671_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_env_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; lean_object* v___y_544_; lean_object* v_a_545_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_562_; lean_object* v_a_563_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v_fileName_619_; lean_object* v_fileMap_620_; lean_object* v_currRecDepth_621_; lean_object* v_ref_622_; lean_object* v_currNamespace_623_; lean_object* v_openDecls_624_; lean_object* v_initHeartbeats_625_; lean_object* v_maxHeartbeats_626_; lean_object* v_quotContext_627_; lean_object* v_currMacroScope_628_; lean_object* v_cancelTk_x3f_629_; uint8_t v_suppressElabErrors_630_; lean_object* v_inheritedTraceOptions_631_; lean_object* v___y_632_; uint8_t v___y_649_; uint8_t v___x_670_; 
v_env_535_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_env_535_);
lean_dec(v___x_517_);
v___x_536_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_537_ = 0;
v___x_538_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_options_520_, v___x_536_, v___x_537_);
v___x_616_ = l_Lean_diagnostics;
v___x_617_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_538_, v___x_616_);
v___x_670_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_535_);
lean_dec_ref(v_env_535_);
if (v___x_670_ == 0)
{
if (v___x_617_ == 0)
{
v_fileName_619_ = v_fileName_518_;
v_fileMap_620_ = v_fileMap_519_;
v_currRecDepth_621_ = v_currRecDepth_521_;
v_ref_622_ = v_ref_522_;
v_currNamespace_623_ = v_currNamespace_523_;
v_openDecls_624_ = v_openDecls_524_;
v_initHeartbeats_625_ = v_initHeartbeats_525_;
v_maxHeartbeats_626_ = v_maxHeartbeats_526_;
v_quotContext_627_ = v_quotContext_527_;
v_currMacroScope_628_ = v_currMacroScope_528_;
v_cancelTk_x3f_629_ = v_cancelTk_x3f_529_;
v_suppressElabErrors_630_ = v_suppressElabErrors_530_;
v_inheritedTraceOptions_631_ = v_inheritedTraceOptions_531_;
v___y_632_ = v___y_515_;
goto v___jp_618_;
}
else
{
v___y_649_ = v___x_670_;
goto v___jp_648_;
}
}
else
{
v___y_649_ = v___x_617_;
goto v___jp_648_;
}
v___jp_539_:
{
lean_object* v___x_546_; double v___x_547_; double v___x_548_; double v___x_549_; double v___x_550_; double v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_546_ = lean_io_mono_nanos_now();
v___x_547_ = lean_float_of_nat(v___y_541_);
v___x_548_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_549_ = lean_float_div(v___x_547_, v___x_548_);
v___x_550_ = lean_float_of_nat(v___x_546_);
v___x_551_ = lean_float_div(v___x_550_, v___x_548_);
v___x_552_ = lean_box_float(v___x_549_);
v___x_553_ = lean_box_float(v___x_551_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_a_545_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6(v___x_509_, v___x_510_, v___x_511_, v___x_538_, v___y_543_, v___y_542_, v___f_512_, v___x_555_, v___y_544_, v___y_540_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v___x_538_);
return v___x_556_;
}
v___jp_557_:
{
lean_object* v___x_564_; double v___x_565_; double v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_564_ = lean_io_get_num_heartbeats();
v___x_565_ = lean_float_of_nat(v___y_560_);
v___x_566_ = lean_float_of_nat(v___x_564_);
v___x_567_ = lean_box_float(v___x_565_);
v___x_568_ = lean_box_float(v___x_566_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_a_563_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6(v___x_509_, v___x_510_, v___x_511_, v___x_538_, v___y_561_, v___y_559_, v___f_512_, v___x_570_, v___y_562_, v___y_558_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___x_538_);
return v___x_571_;
}
v___jp_572_:
{
lean_object* v___x_576_; lean_object* v_a_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__5___redArg(v___y_573_);
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = l_Lean_trace_profiler_useHeartbeats;
v___x_579_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_538_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_io_mono_nanos_now();
v___x_581_ = l_Lean_Compiler_LCNF_main(v_declNames_513_, v___y_575_, v___y_573_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 1);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v___y_540_ = v___y_573_;
v___y_541_ = v___x_580_;
v___y_542_ = v_a_577_;
v___y_543_ = v___y_574_;
v___y_544_ = v___y_575_;
v_a_545_ = v___x_587_;
goto v___jp_539_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v___y_540_ = v___y_573_;
v___y_541_ = v___x_580_;
v___y_542_ = v_a_577_;
v___y_543_ = v___y_574_;
v___y_544_ = v___y_575_;
v_a_545_ = v___x_595_;
goto v___jp_539_;
}
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_io_get_num_heartbeats();
v___x_599_ = l_Lean_Compiler_LCNF_main(v_declNames_513_, v___y_575_, v___y_573_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 1);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v___y_558_ = v___y_573_;
v___y_559_ = v_a_577_;
v___y_560_ = v___x_598_;
v___y_561_ = v___y_574_;
v___y_562_ = v___y_575_;
v_a_563_ = v___x_605_;
goto v___jp_557_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 0);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_558_ = v___y_573_;
v___y_559_ = v_a_577_;
v___y_560_ = v___x_598_;
v___y_561_ = v___y_574_;
v___y_562_ = v___y_575_;
v_a_563_ = v___x_613_;
goto v___jp_557_;
}
}
}
}
}
v___jp_618_:
{
uint8_t v_hasTrace_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v_hasTrace_633_ = lean_ctor_get_uint8(v___x_538_, sizeof(void*)*1);
v___x_634_ = l_Lean_maxRecDepth;
v___x_635_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___x_538_, v___x_634_);
lean_inc_ref(v___x_538_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 13, v_inheritedTraceOptions_631_);
lean_ctor_set(v___x_533_, 12, v_cancelTk_x3f_629_);
lean_ctor_set(v___x_533_, 11, v_currMacroScope_628_);
lean_ctor_set(v___x_533_, 10, v_quotContext_627_);
lean_ctor_set(v___x_533_, 9, v_maxHeartbeats_626_);
lean_ctor_set(v___x_533_, 8, v_initHeartbeats_625_);
lean_ctor_set(v___x_533_, 7, v_openDecls_624_);
lean_ctor_set(v___x_533_, 6, v_currNamespace_623_);
lean_ctor_set(v___x_533_, 5, v_ref_622_);
lean_ctor_set(v___x_533_, 4, v___x_635_);
lean_ctor_set(v___x_533_, 3, v_currRecDepth_621_);
lean_ctor_set(v___x_533_, 2, v___x_538_);
lean_ctor_set(v___x_533_, 1, v_fileMap_620_);
lean_ctor_set(v___x_533_, 0, v_fileName_619_);
v___x_637_ = v___x_533_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fileName_619_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_fileMap_620_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_currRecDepth_621_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v_ref_622_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_currNamespace_623_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_openDecls_624_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_initHeartbeats_625_);
lean_ctor_set(v_reuseFailAlloc_647_, 9, v_maxHeartbeats_626_);
lean_ctor_set(v_reuseFailAlloc_647_, 10, v_quotContext_627_);
lean_ctor_set(v_reuseFailAlloc_647_, 11, v_currMacroScope_628_);
lean_ctor_set(v_reuseFailAlloc_647_, 12, v_cancelTk_x3f_629_);
lean_ctor_set(v_reuseFailAlloc_647_, 13, v_inheritedTraceOptions_631_);
v___x_637_ = v_reuseFailAlloc_647_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*14, v___x_617_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*14 + 1, v_suppressElabErrors_630_);
if (v_hasTrace_633_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_538_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_511_);
lean_dec(v___x_509_);
v___x_638_ = l_Lean_Compiler_LCNF_main(v_declNames_513_, v___x_637_, v___y_632_);
lean_dec_ref(v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v_a_640_; uint8_t v___x_641_; 
lean_inc(v___x_509_);
v___x_639_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__4___redArg(v___x_509_, v___x_637_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_unbox(v_a_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = l_Lean_trace_profiler;
v___x_643_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_538_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v_a_640_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_511_);
lean_dec(v___x_509_);
v___x_644_ = l_Lean_Compiler_LCNF_main(v_declNames_513_, v___x_637_, v___y_632_);
lean_dec_ref(v___x_637_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
v___y_573_ = v___y_632_;
v___y_574_ = v___x_645_;
v___y_575_ = v___x_637_;
goto v___jp_572_;
}
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
v___y_573_ = v___y_632_;
v___y_574_ = v___x_646_;
v___y_575_ = v___x_637_;
goto v___jp_572_;
}
}
}
}
v___jp_648_:
{
if (v___y_649_ == 0)
{
lean_object* v___x_650_; lean_object* v_env_651_; lean_object* v_nextMacroScope_652_; lean_object* v_ngen_653_; lean_object* v_auxDeclNGen_654_; lean_object* v_traceState_655_; lean_object* v_messages_656_; lean_object* v_infoState_657_; lean_object* v_snapshotTasks_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v___x_650_ = lean_st_ref_take(v___y_515_);
v_env_651_ = lean_ctor_get(v___x_650_, 0);
v_nextMacroScope_652_ = lean_ctor_get(v___x_650_, 1);
v_ngen_653_ = lean_ctor_get(v___x_650_, 2);
v_auxDeclNGen_654_ = lean_ctor_get(v___x_650_, 3);
v_traceState_655_ = lean_ctor_get(v___x_650_, 4);
v_messages_656_ = lean_ctor_get(v___x_650_, 6);
v_infoState_657_ = lean_ctor_get(v___x_650_, 7);
v_snapshotTasks_658_ = lean_ctor_get(v___x_650_, 8);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_650_, 5);
lean_dec(v_unused_669_);
v___x_660_ = v___x_650_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snapshotTasks_658_);
lean_inc(v_infoState_657_);
lean_inc(v_messages_656_);
lean_inc(v_traceState_655_);
lean_inc(v_auxDeclNGen_654_);
lean_inc(v_ngen_653_);
lean_inc(v_nextMacroScope_652_);
lean_inc(v_env_651_);
lean_dec(v___x_650_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_662_ = l_Lean_Kernel_enableDiag(v_env_651_, v___x_617_);
v___x_663_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__3, &l_Lean_Compiler_compile___lam__1___closed__3_once, _init_l_Lean_Compiler_compile___lam__1___closed__3);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 5, v___x_663_);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_nextMacroScope_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_ngen_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_auxDeclNGen_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_traceState_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 5, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_667_, 6, v_messages_656_);
lean_ctor_set(v_reuseFailAlloc_667_, 7, v_infoState_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 8, v_snapshotTasks_658_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = lean_st_ref_set(v___y_515_, v___x_665_);
v_fileName_619_ = v_fileName_518_;
v_fileMap_620_ = v_fileMap_519_;
v_currRecDepth_621_ = v_currRecDepth_521_;
v_ref_622_ = v_ref_522_;
v_currNamespace_623_ = v_currNamespace_523_;
v_openDecls_624_ = v_openDecls_524_;
v_initHeartbeats_625_ = v_initHeartbeats_525_;
v_maxHeartbeats_626_ = v_maxHeartbeats_526_;
v_quotContext_627_ = v_quotContext_527_;
v_currMacroScope_628_ = v_currMacroScope_528_;
v_cancelTk_x3f_629_ = v_cancelTk_x3f_529_;
v_suppressElabErrors_630_ = v_suppressElabErrors_530_;
v_inheritedTraceOptions_631_ = v_inheritedTraceOptions_531_;
v___y_632_ = v___y_515_;
goto v___jp_618_;
}
}
}
else
{
v_fileName_619_ = v_fileName_518_;
v_fileMap_620_ = v_fileMap_519_;
v_currRecDepth_621_ = v_currRecDepth_521_;
v_ref_622_ = v_ref_522_;
v_currNamespace_623_ = v_currNamespace_523_;
v_openDecls_624_ = v_openDecls_524_;
v_initHeartbeats_625_ = v_initHeartbeats_525_;
v_maxHeartbeats_626_ = v_maxHeartbeats_526_;
v_quotContext_627_ = v_quotContext_527_;
v_currMacroScope_628_ = v_currMacroScope_528_;
v_cancelTk_x3f_629_ = v_cancelTk_x3f_529_;
v_suppressElabErrors_630_ = v_suppressElabErrors_530_;
v_inheritedTraceOptions_631_ = v_inheritedTraceOptions_531_;
v___y_632_ = v___y_515_;
goto v___jp_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v___f_676_, lean_object* v_declNames_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
uint8_t v___x_6905__boxed_681_; lean_object* v_res_682_; 
v___x_6905__boxed_681_ = lean_unbox(v___x_674_);
v_res_682_ = l_Lean_Compiler_compile___lam__1(v___x_673_, v___x_6905__boxed_681_, v___x_675_, v___f_676_, v_declNames_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_options_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_options_692_ = lean_ctor_get(v_a_689_, 2);
lean_inc_ref(v_declNames_688_);
v___f_693_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_693_, 0, v_declNames_688_);
v___x_694_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_695_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_696_ = 1;
v___x_697_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_698_ = lean_box(v___x_696_);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 8, 5);
lean_closure_set(v___f_699_, 0, v___x_695_);
lean_closure_set(v___f_699_, 1, v___x_698_);
lean_closure_set(v___f_699_, 2, v___x_697_);
lean_closure_set(v___f_699_, 3, v___f_693_);
lean_closure_set(v___f_699_, 4, v_declNames_688_);
v___x_700_ = lean_box(0);
v___x_701_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__7___redArg(v___x_694_, v_options_692_, v___f_699_, v___x_700_, v_a_689_, v_a_690_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Compiler_compile(v_declNames_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9(lean_object* v_00_u03b1_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___redArg(v_x_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9___boxed(lean_object* v_00_u03b1_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__6_spec__9(v_00_u03b1_713_, v_x_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_779_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_780_ = 0;
v___x_781_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_782_ = l_Lean_registerTraceClass(v___x_779_, v___x_780_, v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v___x_782_);
v___x_783_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_784_ = l_Lean_registerTraceClass(v___x_783_, v___x_780_, v___x_781_);
return v___x_784_;
}
else
{
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_786_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Main(builtin);
}
#ifdef __cplusplus
}
#endif

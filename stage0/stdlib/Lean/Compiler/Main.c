// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: public import Lean.Compiler.LCNF
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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
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
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_compile___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "compiling: "};
static const lean_object* l_Lean_Compiler_compile___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_compile___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_compile___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Compiler_compile___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
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
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg(v_cls_21_, v___y_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___boxed(lean_object* v_cls_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1(v_cls_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_30_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((size_t)5ULL);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_unsigned_to_nat(32u);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_38_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0);
v___x_39_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_35_);
lean_ctor_set(v___x_39_, 3, v___x_35_);
lean_ctor_set_usize(v___x_39_, 4, v___x_34_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(lean_object* v___y_40_){
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
v___x_62_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___boxed(lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_74_);
lean_dec(v___y_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___boxed(lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object* v_opts_85_, lean_object* v_opt_86_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_95_, v_opt_96_);
lean_dec_ref(v_opt_96_);
lean_dec_ref(v_opts_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg(lean_object* v_category_99_, lean_object* v_opts_100_, lean_object* v_act_101_, lean_object* v_decl_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_apply_2(v_act_101_, v___y_103_, v___y_104_);
v___x_107_ = l_Lean_profileitIOUnsafe___redArg(v_category_99_, v_opts_100_, v___x_106_, v_decl_102_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg___boxed(lean_object* v_category_108_, lean_object* v_opts_109_, lean_object* v_act_110_, lean_object* v_decl_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg(v_category_108_, v_opts_109_, v_act_110_, v_decl_111_, v___y_112_, v___y_113_);
lean_dec_ref(v_opts_109_);
lean_dec_ref(v_category_108_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5(lean_object* v_00_u03b1_116_, lean_object* v_category_117_, lean_object* v_opts_118_, lean_object* v_act_119_, lean_object* v_decl_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg(v_category_117_, v_opts_118_, v_act_119_, v_decl_120_, v___y_121_, v___y_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_00_u03b1_125_, lean_object* v_category_126_, lean_object* v_opts_127_, lean_object* v_act_128_, lean_object* v_decl_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5(v_00_u03b1_125_, v_category_126_, v_opts_127_, v_act_128_, v_decl_129_, v___y_130_, v___y_131_);
lean_dec_ref(v_opts_127_);
lean_dec_ref(v_category_126_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
if (lean_obj_tag(v_a_134_) == 0)
{
lean_object* v___x_136_; 
v___x_136_ = l_List_reverse___redArg(v_a_135_);
return v___x_136_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_147_; 
v_head_137_ = lean_ctor_get(v_a_134_, 0);
v_tail_138_ = lean_ctor_get(v_a_134_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_a_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_140_ = v_a_134_;
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_tail_138_);
lean_inc(v_head_137_);
lean_dec(v_a_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = l_Lean_MessageData_ofName(v_head_137_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_a_135_);
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_a_135_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v_a_134_ = v_tail_138_;
v_a_135_ = v___x_144_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Compiler_compile___lam__0___closed__0));
v___x_150_ = l_Lean_stringToMessageData(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object* v_declNames_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_156_ = lean_obj_once(&l_Lean_Compiler_compile___lam__0___closed__1, &l_Lean_Compiler_compile___lam__0___closed__1_once, _init_l_Lean_Compiler_compile___lam__0___closed__1);
v___x_157_ = lean_array_to_list(v_declNames_151_);
v___x_158_ = lean_box(0);
v___x_159_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_157_, v___x_158_);
v___x_160_ = l_Lean_MessageData_ofList(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_156_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* v_declNames_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_compile___lam__0(v_declNames_163_, v_x_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec_ref(v_x_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 1);
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v_x_169_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v_x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 0);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg___boxed(lean_object* v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(v_x_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7(lean_object* v_opts_190_, lean_object* v_opt_191_){
_start:
{
lean_object* v_name_192_; lean_object* v_defValue_193_; lean_object* v_map_194_; lean_object* v___x_195_; 
v_name_192_ = lean_ctor_get(v_opt_191_, 0);
v_defValue_193_ = lean_ctor_get(v_opt_191_, 1);
v_map_194_ = lean_ctor_get(v_opts_190_, 0);
v___x_195_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_194_, v_name_192_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_inc(v_defValue_193_);
return v_defValue_193_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref(v___x_195_);
if (lean_obj_tag(v_val_196_) == 3)
{
lean_object* v_v_197_; 
v_v_197_ = lean_ctor_get(v_val_196_, 0);
lean_inc(v_v_197_);
lean_dec_ref(v_val_196_);
return v_v_197_;
}
else
{
lean_dec(v_val_196_);
lean_inc(v_defValue_193_);
return v_defValue_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7___boxed(lean_object* v_opts_198_, lean_object* v_opt_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7(v_opts_198_, v_opt_199_);
lean_dec_ref(v_opt_199_);
lean_dec_ref(v_opts_198_);
return v_res_200_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object* v_e_201_){
_start:
{
if (lean_obj_tag(v_e_201_) == 0)
{
uint8_t v___x_202_; 
v___x_202_ = 2;
return v___x_202_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object* v_e_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_e_204_);
lean_dec_ref(v_e_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7(size_t v_sz_207_, size_t v_i_208_, lean_object* v_bs_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_usize_dec_lt(v_i_208_, v_sz_207_);
if (v___x_210_ == 0)
{
return v_bs_209_;
}
else
{
lean_object* v_v_211_; lean_object* v_msg_212_; lean_object* v___x_213_; lean_object* v_bs_x27_214_; size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v_v_211_ = lean_array_uget_borrowed(v_bs_209_, v_i_208_);
v_msg_212_ = lean_ctor_get(v_v_211_, 1);
lean_inc_ref(v_msg_212_);
v___x_213_ = lean_unsigned_to_nat(0u);
v_bs_x27_214_ = lean_array_uset(v_bs_209_, v_i_208_, v___x_213_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_add(v_i_208_, v___x_215_);
v___x_217_ = lean_array_uset(v_bs_x27_214_, v_i_208_, v_msg_212_);
v_i_208_ = v___x_216_;
v_bs_209_ = v___x_217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7___boxed(lean_object* v_sz_219_, lean_object* v_i_220_, lean_object* v_bs_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_219_);
lean_dec(v_sz_219_);
v_i_boxed_223_ = lean_unbox_usize(v_i_220_);
lean_dec(v_i_220_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7(v_sz_boxed_222_, v_i_boxed_223_, v_bs_221_);
return v_res_224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set(v___x_230_, 3, v___x_228_);
lean_ctor_set(v___x_230_, 4, v___x_228_);
lean_ctor_set(v___x_230_, 5, v___x_228_);
lean_ctor_set(v___x_230_, 6, v___x_228_);
lean_ctor_set(v___x_230_, 7, v___x_228_);
lean_ctor_set(v___x_230_, 8, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(32u);
v___x_232_ = lean_mk_empty_array_with_capacity(v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4(void){
_start:
{
size_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_234_ = ((size_t)5ULL);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_unsigned_to_nat(32u);
v___x_237_ = lean_mk_empty_array_with_capacity(v___x_236_);
v___x_238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__3);
v___x_239_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_235_);
lean_ctor_set(v___x_239_, 3, v___x_235_);
lean_ctor_set_usize(v___x_239_, 4, v___x_234_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_box(1);
v___x_241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__4);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__1);
v___x_243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_env_249_; lean_object* v_options_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_248_ = lean_st_ref_get(v___y_246_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_env_249_);
lean_dec(v___x_248_);
v_options_250_ = lean_ctor_get(v___y_245_, 2);
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__2);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___closed__5);
lean_inc_ref(v_options_250_);
v___x_253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_253_, 0, v_env_249_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
lean_ctor_set(v___x_253_, 3, v_options_250_);
v___x_254_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_msgData_244_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8(v_msgData_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object* v_oldTraces_261_, lean_object* v_data_262_, lean_object* v_ref_263_, lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_fileName_268_; lean_object* v_fileMap_269_; lean_object* v_options_270_; lean_object* v_currRecDepth_271_; lean_object* v_maxRecDepth_272_; lean_object* v_ref_273_; lean_object* v_currNamespace_274_; lean_object* v_openDecls_275_; lean_object* v_initHeartbeats_276_; lean_object* v_maxHeartbeats_277_; lean_object* v_quotContext_278_; lean_object* v_currMacroScope_279_; uint8_t v_diag_280_; lean_object* v_cancelTk_x3f_281_; uint8_t v_suppressElabErrors_282_; lean_object* v_inheritedTraceOptions_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_338_; 
v_fileName_268_ = lean_ctor_get(v___y_265_, 0);
v_fileMap_269_ = lean_ctor_get(v___y_265_, 1);
v_options_270_ = lean_ctor_get(v___y_265_, 2);
v_currRecDepth_271_ = lean_ctor_get(v___y_265_, 3);
v_maxRecDepth_272_ = lean_ctor_get(v___y_265_, 4);
v_ref_273_ = lean_ctor_get(v___y_265_, 5);
v_currNamespace_274_ = lean_ctor_get(v___y_265_, 6);
v_openDecls_275_ = lean_ctor_get(v___y_265_, 7);
v_initHeartbeats_276_ = lean_ctor_get(v___y_265_, 8);
v_maxHeartbeats_277_ = lean_ctor_get(v___y_265_, 9);
v_quotContext_278_ = lean_ctor_get(v___y_265_, 10);
v_currMacroScope_279_ = lean_ctor_get(v___y_265_, 11);
v_diag_280_ = lean_ctor_get_uint8(v___y_265_, sizeof(void*)*14);
v_cancelTk_x3f_281_ = lean_ctor_get(v___y_265_, 12);
v_suppressElabErrors_282_ = lean_ctor_get_uint8(v___y_265_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_283_ = lean_ctor_get(v___y_265_, 13);
v_isSharedCheck_338_ = !lean_is_exclusive(v___y_265_);
if (v_isSharedCheck_338_ == 0)
{
v___x_285_ = v___y_265_;
v_isShared_286_ = v_isSharedCheck_338_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_inheritedTraceOptions_283_);
lean_inc(v_cancelTk_x3f_281_);
lean_inc(v_currMacroScope_279_);
lean_inc(v_quotContext_278_);
lean_inc(v_maxHeartbeats_277_);
lean_inc(v_initHeartbeats_276_);
lean_inc(v_openDecls_275_);
lean_inc(v_currNamespace_274_);
lean_inc(v_ref_273_);
lean_inc(v_maxRecDepth_272_);
lean_inc(v_currRecDepth_271_);
lean_inc(v_options_270_);
lean_inc(v_fileMap_269_);
lean_inc(v_fileName_268_);
lean_dec(v___y_265_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_338_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v_traceState_288_; lean_object* v_traces_289_; lean_object* v_ref_290_; lean_object* v___x_292_; 
v___x_287_ = lean_st_ref_get(v___y_266_);
v_traceState_288_ = lean_ctor_get(v___x_287_, 4);
lean_inc_ref(v_traceState_288_);
lean_dec(v___x_287_);
v_traces_289_ = lean_ctor_get(v_traceState_288_, 0);
lean_inc_ref(v_traces_289_);
lean_dec_ref(v_traceState_288_);
v_ref_290_ = l_Lean_replaceRef(v_ref_263_, v_ref_273_);
lean_dec(v_ref_273_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 5, v_ref_290_);
v___x_292_ = v___x_285_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_fileName_268_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_fileMap_269_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_options_270_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_currRecDepth_271_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_maxRecDepth_272_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v_ref_290_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_currNamespace_274_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_openDecls_275_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_initHeartbeats_276_);
lean_ctor_set(v_reuseFailAlloc_337_, 9, v_maxHeartbeats_277_);
lean_ctor_set(v_reuseFailAlloc_337_, 10, v_quotContext_278_);
lean_ctor_set(v_reuseFailAlloc_337_, 11, v_currMacroScope_279_);
lean_ctor_set(v_reuseFailAlloc_337_, 12, v_cancelTk_x3f_281_);
lean_ctor_set(v_reuseFailAlloc_337_, 13, v_inheritedTraceOptions_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_337_, sizeof(void*)*14, v_diag_280_);
lean_ctor_set_uint8(v_reuseFailAlloc_337_, sizeof(void*)*14 + 1, v_suppressElabErrors_282_);
v___x_292_ = v_reuseFailAlloc_337_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; size_t v_sz_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v_msg_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_336_; 
v___x_293_ = l_Lean_PersistentArray_toArray___redArg(v_traces_289_);
lean_dec_ref(v_traces_289_);
v_sz_294_ = lean_array_size(v___x_293_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__7(v_sz_294_, v___x_295_, v___x_293_);
v_msg_297_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_297_, 0, v_data_262_);
lean_ctor_set(v_msg_297_, 1, v_msg_264_);
lean_ctor_set(v_msg_297_, 2, v___x_296_);
v___x_298_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_spec__8(v_msg_297_, v___x_292_, v___y_266_);
lean_dec_ref(v___x_292_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_336_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_336_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_336_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v_traceState_304_; lean_object* v_env_305_; lean_object* v_nextMacroScope_306_; lean_object* v_ngen_307_; lean_object* v_auxDeclNGen_308_; lean_object* v_cache_309_; lean_object* v_messages_310_; lean_object* v_infoState_311_; lean_object* v_snapshotTasks_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_335_; 
v___x_303_ = lean_st_ref_take(v___y_266_);
v_traceState_304_ = lean_ctor_get(v___x_303_, 4);
v_env_305_ = lean_ctor_get(v___x_303_, 0);
v_nextMacroScope_306_ = lean_ctor_get(v___x_303_, 1);
v_ngen_307_ = lean_ctor_get(v___x_303_, 2);
v_auxDeclNGen_308_ = lean_ctor_get(v___x_303_, 3);
v_cache_309_ = lean_ctor_get(v___x_303_, 5);
v_messages_310_ = lean_ctor_get(v___x_303_, 6);
v_infoState_311_ = lean_ctor_get(v___x_303_, 7);
v_snapshotTasks_312_ = lean_ctor_get(v___x_303_, 8);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_335_ == 0)
{
v___x_314_ = v___x_303_;
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_snapshotTasks_312_);
lean_inc(v_infoState_311_);
lean_inc(v_messages_310_);
lean_inc(v_cache_309_);
lean_inc(v_traceState_304_);
lean_inc(v_auxDeclNGen_308_);
lean_inc(v_ngen_307_);
lean_inc(v_nextMacroScope_306_);
lean_inc(v_env_305_);
lean_dec(v___x_303_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint64_t v_tid_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_333_; 
v_tid_316_ = lean_ctor_get_uint64(v_traceState_304_, sizeof(void*)*1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_traceState_304_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_traceState_304_, 0);
lean_dec(v_unused_334_);
v___x_318_ = v_traceState_304_;
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_traceState_304_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_ref_263_);
lean_ctor_set(v___x_320_, 1, v_a_299_);
v___x_321_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_261_, v___x_320_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_321_);
lean_ctor_set_uint64(v_reuseFailAlloc_332_, sizeof(void*)*1, v_tid_316_);
v___x_323_ = v_reuseFailAlloc_332_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_323_);
v___x_325_ = v___x_314_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_env_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_ngen_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_auxDeclNGen_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_messages_310_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_infoState_311_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_snapshotTasks_312_);
v___x_325_ = v_reuseFailAlloc_331_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_st_ref_set(v___y_266_, v___x_325_);
v___x_327_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_327_);
v___x_329_ = v___x_301_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object* v_oldTraces_339_, lean_object* v_data_340_, lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_oldTraces_339_, v_data_340_, v_ref_341_, v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2(void){
_start:
{
lean_object* v___x_350_; double v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_float_of_nat(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5(void){
_start:
{
lean_object* v___x_355_; double v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1000u);
v___x_356_ = lean_float_of_nat(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_357_, uint8_t v_collapsed_358_, lean_object* v_tag_359_, lean_object* v_opts_360_, uint8_t v_clsEnabled_361_, lean_object* v_oldTraces_362_, lean_object* v_msg_363_, lean_object* v_resStartStop_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_459_; 
v_fst_368_ = lean_ctor_get(v_resStartStop_364_, 0);
v_snd_369_ = lean_ctor_get(v_resStartStop_364_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_resStartStop_364_);
if (v_isSharedCheck_459_ == 0)
{
v___x_371_ = v_resStartStop_364_;
v_isShared_372_ = v_isSharedCheck_459_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_resStartStop_364_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_459_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v_data_376_; lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_458_; 
v_fst_379_ = lean_ctor_get(v_snd_369_, 0);
v_snd_380_ = lean_ctor_get(v_snd_369_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_snd_369_);
if (v_isSharedCheck_458_ == 0)
{
v___x_382_ = v_snd_369_;
v_isShared_383_ = v_isSharedCheck_458_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_380_);
lean_inc(v_fst_379_);
lean_dec(v_snd_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_458_;
goto v_resetjp_381_;
}
v___jp_373_:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_oldTraces_362_, v_data_376_, v___y_375_, v___y_374_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_377_);
v___x_378_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(v_fst_368_);
return v___x_378_;
}
else
{
lean_dec(v_fst_368_);
return v___x_377_;
}
}
v_resetjp_381_:
{
lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___y_387_; lean_object* v_a_388_; uint8_t v___y_412_; double v___y_443_; 
v___x_384_ = l_Lean_trace_profiler;
v___x_385_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_360_, v___x_384_);
if (v___x_385_ == 0)
{
v___y_412_ = v___x_385_;
goto v___jp_411_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = l_Lean_trace_profiler_useHeartbeats;
v___x_449_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_360_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; double v___x_452_; double v___x_453_; double v___x_454_; 
v___x_450_ = l_Lean_trace_profiler_threshold;
v___x_451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7(v_opts_360_, v___x_450_);
v___x_452_ = lean_float_of_nat(v___x_451_);
v___x_453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__5);
v___x_454_ = lean_float_div(v___x_452_, v___x_453_);
v___y_443_ = v___x_454_;
goto v___jp_442_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; 
v___x_455_ = l_Lean_trace_profiler_threshold;
v___x_456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__7(v_opts_360_, v___x_455_);
v___x_457_ = lean_float_of_nat(v___x_456_);
v___y_443_ = v___x_457_;
goto v___jp_442_;
}
}
v___jp_386_:
{
uint8_t v_result_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v_result_389_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_fst_368_);
v___x_390_ = l_Lean_TraceResult_toEmoji(v_result_389_);
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
v___x_392_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 7);
lean_ctor_set(v___x_382_, 1, v___x_392_);
lean_ctor_set(v___x_382_, 0, v___x_391_);
v___x_394_ = v___x_382_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_405_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v_m_396_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 7);
lean_ctor_set(v___x_371_, 1, v_a_388_);
lean_ctor_set(v___x_371_, 0, v___x_394_);
v_m_396_ = v___x_371_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_388_);
v_m_396_ = v_reuseFailAlloc_404_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; double v___x_399_; lean_object* v_data_400_; 
v___x_397_ = lean_box(v_result_389_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2);
lean_inc_ref(v_tag_359_);
lean_inc_ref(v___x_398_);
lean_inc(v_cls_357_);
v_data_400_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_400_, 0, v_cls_357_);
lean_ctor_set(v_data_400_, 1, v___x_398_);
lean_ctor_set(v_data_400_, 2, v_tag_359_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3, v___x_399_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3 + 8, v___x_399_);
lean_ctor_set_uint8(v_data_400_, sizeof(void*)*3 + 16, v_collapsed_358_);
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_398_);
lean_dec(v_snd_380_);
lean_dec(v_fst_379_);
lean_dec_ref(v_tag_359_);
lean_dec(v_cls_357_);
v___y_374_ = v_m_396_;
v___y_375_ = v___y_387_;
v_data_376_ = v_data_400_;
goto v___jp_373_;
}
else
{
lean_object* v_data_401_; double v___x_402_; double v___x_403_; 
lean_dec_ref(v_data_400_);
v_data_401_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_401_, 0, v_cls_357_);
lean_ctor_set(v_data_401_, 1, v___x_398_);
lean_ctor_set(v_data_401_, 2, v_tag_359_);
v___x_402_ = lean_unbox_float(v_fst_379_);
lean_dec(v_fst_379_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3, v___x_402_);
v___x_403_ = lean_unbox_float(v_snd_380_);
lean_dec(v_snd_380_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3 + 8, v___x_403_);
lean_ctor_set_uint8(v_data_401_, sizeof(void*)*3 + 16, v_collapsed_358_);
v___y_374_ = v_m_396_;
v___y_375_ = v___y_387_;
v_data_376_ = v_data_401_;
goto v___jp_373_;
}
}
}
}
v___jp_406_:
{
lean_object* v_ref_407_; lean_object* v___x_408_; 
v_ref_407_ = lean_ctor_get(v___y_365_, 5);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v_fst_368_);
v___x_408_ = lean_apply_4(v_msg_363_, v_fst_368_, v___y_365_, v___y_366_, lean_box(0));
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref(v___x_408_);
lean_inc(v_ref_407_);
v___y_387_ = v_ref_407_;
v_a_388_ = v_a_409_;
goto v___jp_386_;
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v___x_408_);
v___x_410_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__4);
lean_inc(v_ref_407_);
v___y_387_ = v_ref_407_;
v_a_388_ = v___x_410_;
goto v___jp_386_;
}
}
v___jp_411_:
{
if (v_clsEnabled_361_ == 0)
{
if (v___y_412_ == 0)
{
lean_object* v___x_413_; lean_object* v_traceState_414_; lean_object* v_env_415_; lean_object* v_nextMacroScope_416_; lean_object* v_ngen_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_cache_419_; lean_object* v_messages_420_; lean_object* v_infoState_421_; lean_object* v_snapshotTasks_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_382_);
lean_dec(v_snd_380_);
lean_dec(v_fst_379_);
lean_del_object(v___x_371_);
lean_dec_ref(v___y_365_);
lean_dec_ref(v_msg_363_);
lean_dec_ref(v_tag_359_);
lean_dec(v_cls_357_);
v___x_413_ = lean_st_ref_take(v___y_366_);
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
v___x_431_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_362_, v_traces_427_);
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
v___x_436_ = lean_st_ref_set(v___y_366_, v___x_435_);
lean_dec(v___y_366_);
v___x_437_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(v_fst_368_);
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
v___x_444_ = lean_unbox_float(v_snd_380_);
v___x_445_ = lean_unbox_float(v_fst_379_);
v___x_446_ = lean_float_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_float_decLt(v___y_443_, v___x_446_);
v___y_412_ = v___x_447_;
goto v___jp_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_460_, lean_object* v_collapsed_461_, lean_object* v_tag_462_, lean_object* v_opts_463_, lean_object* v_clsEnabled_464_, lean_object* v_oldTraces_465_, lean_object* v_msg_466_, lean_object* v_resStartStop_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v_collapsed_boxed_471_; uint8_t v_clsEnabled_boxed_472_; lean_object* v_res_473_; 
v_collapsed_boxed_471_ = lean_unbox(v_collapsed_461_);
v_clsEnabled_boxed_472_ = lean_unbox(v_clsEnabled_464_);
v_res_473_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_460_, v_collapsed_boxed_471_, v_tag_462_, v_opts_463_, v_clsEnabled_boxed_472_, v_oldTraces_465_, v_msg_466_, v_resStartStop_467_, v___y_468_, v___y_469_);
lean_dec_ref(v_opts_463_);
return v_res_473_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_474_; double v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1000000000u);
v___x_475_ = lean_float_of_nat(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v_declNames_476_, lean_object* v___x_477_, lean_object* v___x_478_, uint8_t v___x_479_, lean_object* v___x_480_, lean_object* v___f_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_options_485_; uint8_t v_hasTrace_486_; 
v_options_485_ = lean_ctor_get(v___y_482_, 2);
v_hasTrace_486_ = lean_ctor_get_uint8(v_options_485_, sizeof(void*)*1);
if (v_hasTrace_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v___f_481_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_478_);
v___x_487_ = l_Lean_Compiler_LCNF_compile(v_declNames_476_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_495_);
v___x_489_ = v___x_487_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_dec(v___x_487_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_477_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_477_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v_a_509_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v_a_525_; uint8_t v___x_576_; 
lean_inc(v___x_478_);
v___x_504_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_compile_spec__1___redArg(v___x_478_, v___y_482_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_576_ = lean_unbox(v_a_505_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = l_Lean_trace_profiler;
v___x_578_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_options_485_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v_a_505_);
lean_dec_ref(v___f_481_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_478_);
v___x_579_ = l_Lean_Compiler_LCNF_compile(v_declNames_476_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_587_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_477_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_477_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_579_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_579_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_inc_ref(v_options_485_);
goto v___jp_535_;
}
}
else
{
lean_inc_ref(v_options_485_);
goto v___jp_535_;
}
v___jp_506_:
{
lean_object* v___x_510_; double v___x_511_; double v___x_512_; double v___x_513_; double v___x_514_; double v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; 
v___x_510_ = lean_io_mono_nanos_now();
v___x_511_ = lean_float_of_nat(v___y_508_);
v___x_512_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_513_ = lean_float_div(v___x_511_, v___x_512_);
v___x_514_ = lean_float_of_nat(v___x_510_);
v___x_515_ = lean_float_div(v___x_514_, v___x_512_);
v___x_516_ = lean_box_float(v___x_513_);
v___x_517_ = lean_box_float(v___x_515_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_a_509_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_478_, v___x_479_, v___x_480_, v_options_485_, v___x_520_, v___y_507_, v___f_481_, v___x_519_, v___y_482_, v___y_483_);
lean_dec_ref(v_options_485_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_526_; double v___x_527_; double v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_526_ = lean_io_get_num_heartbeats();
v___x_527_ = lean_float_of_nat(v___y_523_);
v___x_528_ = lean_float_of_nat(v___x_526_);
v___x_529_ = lean_box_float(v___x_527_);
v___x_530_ = lean_box_float(v___x_528_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_525_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
v___x_534_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_478_, v___x_479_, v___x_480_, v_options_485_, v___x_533_, v___y_524_, v___f_481_, v___x_532_, v___y_482_, v___y_483_);
lean_dec_ref(v_options_485_);
return v___x_534_;
}
v___jp_535_:
{
lean_object* v___x_536_; lean_object* v_a_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_536_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_483_);
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref(v___x_536_);
v___x_538_ = l_Lean_trace_profiler_useHeartbeats;
v___x_539_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_options_485_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_io_mono_nanos_now();
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
v___x_541_ = l_Lean_Compiler_LCNF_compile(v_declNames_476_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 1);
lean_ctor_set(v___x_543_, 0, v___x_477_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_477_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_507_ = v_a_537_;
v___y_508_ = v___x_540_;
v_a_509_ = v___x_546_;
goto v___jp_506_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 0);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v___y_507_ = v_a_537_;
v___y_508_ = v___x_540_;
v_a_509_ = v___x_555_;
goto v___jp_506_;
}
}
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_io_get_num_heartbeats();
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
v___x_559_ = l_Lean_Compiler_LCNF_compile(v_declNames_476_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v___x_559_, 0);
lean_dec(v_unused_567_);
v___x_561_ = v___x_559_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_dec(v___x_559_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 1);
lean_ctor_set(v___x_561_, 0, v___x_477_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_477_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_523_ = v___x_558_;
v___y_524_ = v_a_537_;
v_a_525_ = v___x_564_;
goto v___jp_522_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_559_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_559_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_523_ = v___x_558_;
v___y_524_ = v_a_537_;
v_a_525_ = v___x_573_;
goto v___jp_522_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v_declNames_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v___f_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
uint8_t v___x_7047__boxed_605_; lean_object* v_res_606_; 
v___x_7047__boxed_605_ = lean_unbox(v___x_599_);
v_res_606_ = l_Lean_Compiler_compile___lam__1(v_declNames_596_, v___x_597_, v___x_598_, v___x_7047__boxed_605_, v___x_600_, v___f_601_, v___y_602_, v___y_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_options_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_options_616_ = lean_ctor_get(v_a_613_, 2);
lean_inc_ref(v_options_616_);
lean_inc_ref(v_declNames_612_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_617_, 0, v_declNames_612_);
v___x_618_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_619_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_620_ = lean_box(0);
v___x_621_ = 1;
v___x_622_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_623_ = lean_box(v___x_621_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_624_, 0, v_declNames_612_);
lean_closure_set(v___f_624_, 1, v___x_620_);
lean_closure_set(v___f_624_, 2, v___x_619_);
lean_closure_set(v___f_624_, 3, v___x_623_);
lean_closure_set(v___f_624_, 4, v___x_622_);
lean_closure_set(v___f_624_, 5, v___f_617_);
v___x_625_ = lean_box(0);
v___x_626_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__5___redArg(v___x_618_, v_options_616_, v___f_624_, v___x_625_, v_a_613_, v_a_614_);
lean_dec_ref(v_options_616_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Compiler_compile(v_declNames_627_, v_a_628_, v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(lean_object* v_00_u03b1_632_, lean_object* v_x_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___redArg(v_x_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___boxed(lean_object* v_00_u03b1_638_, lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_00_u03b1_638_, v_x_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_705_ = 0;
v___x_706_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_707_ = l_Lean_registerTraceClass(v___x_704_, v___x_705_, v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref(v___x_707_);
v___x_708_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_709_ = l_Lean_registerTraceClass(v___x_708_, v___x_705_, v___x_706_);
return v___x_709_;
}
else
{
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_711_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF(builtin);
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

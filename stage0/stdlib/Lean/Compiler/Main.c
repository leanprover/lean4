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
lean_object* l_Lean_Compiler_LCNF_main(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_compile___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "compiling: "};
static const lean_object* l_Lean_Compiler_compile___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_compile___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_compile___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Compiler_compile___lam__1___closed__0;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__1;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__2;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(32u);
v___x_27_ = lean_mk_empty_array_with_capacity(v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_29_ = ((size_t)5ULL);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_unsigned_to_nat(32u);
v___x_32_ = lean_mk_empty_array_with_capacity(v___x_31_);
v___x_33_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0);
v___x_34_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
lean_ctor_set(v___x_34_, 2, v___x_30_);
lean_ctor_set(v___x_34_, 3, v___x_30_);
lean_ctor_set_usize(v___x_34_, 4, v___x_29_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; lean_object* v_traceState_38_; lean_object* v_traces_39_; lean_object* v___x_40_; lean_object* v_traceState_41_; lean_object* v_env_42_; lean_object* v_nextMacroScope_43_; lean_object* v_ngen_44_; lean_object* v_auxDeclNGen_45_; lean_object* v_cache_46_; lean_object* v_messages_47_; lean_object* v_infoState_48_; lean_object* v_snapshotTasks_49_; lean_object* v_newDecls_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_69_; 
v___x_37_ = lean_st_ref_get(v___y_35_);
v_traceState_38_ = lean_ctor_get(v___x_37_, 4);
lean_inc_ref(v_traceState_38_);
lean_dec(v___x_37_);
v_traces_39_ = lean_ctor_get(v_traceState_38_, 0);
lean_inc_ref(v_traces_39_);
lean_dec_ref(v_traceState_38_);
v___x_40_ = lean_st_ref_take(v___y_35_);
v_traceState_41_ = lean_ctor_get(v___x_40_, 4);
v_env_42_ = lean_ctor_get(v___x_40_, 0);
v_nextMacroScope_43_ = lean_ctor_get(v___x_40_, 1);
v_ngen_44_ = lean_ctor_get(v___x_40_, 2);
v_auxDeclNGen_45_ = lean_ctor_get(v___x_40_, 3);
v_cache_46_ = lean_ctor_get(v___x_40_, 5);
v_messages_47_ = lean_ctor_get(v___x_40_, 6);
v_infoState_48_ = lean_ctor_get(v___x_40_, 7);
v_snapshotTasks_49_ = lean_ctor_get(v___x_40_, 8);
v_newDecls_50_ = lean_ctor_get(v___x_40_, 9);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_69_ == 0)
{
v___x_52_ = v___x_40_;
v_isShared_53_ = v_isSharedCheck_69_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_newDecls_50_);
lean_inc(v_snapshotTasks_49_);
lean_inc(v_infoState_48_);
lean_inc(v_messages_47_);
lean_inc(v_cache_46_);
lean_inc(v_traceState_41_);
lean_inc(v_auxDeclNGen_45_);
lean_inc(v_ngen_44_);
lean_inc(v_nextMacroScope_43_);
lean_inc(v_env_42_);
lean_dec(v___x_40_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_69_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
uint64_t v_tid_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_67_; 
v_tid_54_ = lean_ctor_get_uint64(v_traceState_41_, sizeof(void*)*1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_traceState_41_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v_traceState_41_, 0);
lean_dec(v_unused_68_);
v___x_56_ = v_traceState_41_;
v_isShared_57_ = v_isSharedCheck_67_;
goto v_resetjp_55_;
}
else
{
lean_dec(v_traceState_41_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_67_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_60_ = v___x_56_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_58_);
lean_ctor_set_uint64(v_reuseFailAlloc_66_, sizeof(void*)*1, v_tid_54_);
v___x_60_ = v_reuseFailAlloc_66_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_62_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v___x_60_);
v___x_62_ = v___x_52_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_env_42_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_nextMacroScope_43_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_ngen_44_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_auxDeclNGen_45_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_65_, 5, v_cache_46_);
lean_ctor_set(v_reuseFailAlloc_65_, 6, v_messages_47_);
lean_ctor_set(v_reuseFailAlloc_65_, 7, v_infoState_48_);
lean_ctor_set(v_reuseFailAlloc_65_, 8, v_snapshotTasks_49_);
lean_ctor_set(v_reuseFailAlloc_65_, 9, v_newDecls_50_);
v___x_62_ = v_reuseFailAlloc_65_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_st_ref_set(v___y_35_, v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_traces_39_);
return v___x_64_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___boxed(lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_70_);
lean_dec(v___y_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(lean_object* v_category_81_, lean_object* v_opts_82_, lean_object* v_act_83_, lean_object* v_decl_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_88_ = lean_apply_2(v_act_83_, v___y_85_, v___y_86_);
v___x_89_ = l_Lean_profileitIOUnsafe___redArg(v_category_81_, v_opts_82_, v___x_88_, v_decl_84_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg___boxed(lean_object* v_category_90_, lean_object* v_opts_91_, lean_object* v_act_92_, lean_object* v_decl_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_90_, v_opts_91_, v_act_92_, v_decl_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec_ref(v_opts_91_);
lean_dec_ref(v_category_90_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(lean_object* v_00_u03b1_98_, lean_object* v_category_99_, lean_object* v_opts_100_, lean_object* v_act_101_, lean_object* v_decl_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_99_, v_opts_100_, v_act_101_, v_decl_102_, v___y_103_, v___y_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___boxed(lean_object* v_00_u03b1_107_, lean_object* v_category_108_, lean_object* v_opts_109_, lean_object* v_act_110_, lean_object* v_decl_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(v_00_u03b1_107_, v_category_108_, v_opts_109_, v_act_110_, v_decl_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec_ref(v_opts_109_);
lean_dec_ref(v_category_108_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
if (lean_obj_tag(v_a_116_) == 0)
{
lean_object* v___x_118_; 
v___x_118_ = l_List_reverse___redArg(v_a_117_);
return v___x_118_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_head_119_ = lean_ctor_get(v_a_116_, 0);
v_tail_120_ = lean_ctor_get(v_a_116_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_a_116_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v_a_116_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_tail_120_);
lean_inc(v_head_119_);
lean_dec(v_a_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = l_Lean_MessageData_ofName(v_head_119_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_a_117_);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_a_117_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_a_116_ = v_tail_120_;
v_a_117_ = v___x_126_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Compiler_compile___lam__0___closed__0));
v___x_132_ = l_Lean_stringToMessageData(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object* v_declNames_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_138_ = lean_obj_once(&l_Lean_Compiler_compile___lam__0___closed__1, &l_Lean_Compiler_compile___lam__0___closed__1_once, _init_l_Lean_Compiler_compile___lam__0___closed__1);
v___x_139_ = lean_array_to_list(v_declNames_133_);
v___x_140_ = lean_box(0);
v___x_141_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_139_, v___x_140_);
v___x_142_ = l_Lean_MessageData_ofList(v___x_141_);
v___x_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_138_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* v_declNames_145_, lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Compiler_compile___lam__0(v_declNames_145_, v_x_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec_ref(v_x_146_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(lean_object* v_o_154_, lean_object* v_k_155_, uint8_t v_v_156_){
_start:
{
lean_object* v_map_157_; uint8_t v_hasTrace_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_172_; 
v_map_157_ = lean_ctor_get(v_o_154_, 0);
v_hasTrace_158_ = lean_ctor_get_uint8(v_o_154_, sizeof(void*)*1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_o_154_);
if (v_isSharedCheck_172_ == 0)
{
v___x_160_ = v_o_154_;
v_isShared_161_ = v_isSharedCheck_172_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_map_157_);
lean_dec(v_o_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_172_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_162_, 0, v_v_156_);
lean_inc(v_k_155_);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_155_, v___x_162_, v_map_157_);
if (v_hasTrace_158_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_167_; 
v___x_164_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
v___x_165_ = l_Lean_Name_isPrefixOf(v___x_164_, v_k_155_);
lean_dec(v_k_155_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_163_);
v___x_167_ = v___x_160_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_163_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_165_);
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; 
lean_dec(v_k_155_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_163_);
v___x_170_ = v___x_160_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, sizeof(void*)*1, v_hasTrace_158_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(lean_object* v_o_173_, lean_object* v_k_174_, lean_object* v_v_175_){
_start:
{
uint8_t v_v_boxed_176_; lean_object* v_res_177_; 
v_v_boxed_176_ = lean_unbox(v_v_175_);
v_res_177_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_o_173_, v_k_174_, v_v_boxed_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(lean_object* v_opts_178_, lean_object* v_opt_179_, uint8_t v_val_180_){
_start:
{
lean_object* v_name_181_; lean_object* v___x_182_; 
v_name_181_ = lean_ctor_get(v_opt_179_, 0);
lean_inc(v_name_181_);
lean_dec_ref(v_opt_179_);
v___x_182_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_opts_178_, v_name_181_, v_val_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(lean_object* v_opts_183_, lean_object* v_opt_184_, lean_object* v_val_185_){
_start:
{
uint8_t v_val_boxed_186_; lean_object* v_res_187_; 
v_val_boxed_186_ = lean_unbox(v_val_185_);
v_res_187_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_opts_183_, v_opt_184_, v_val_boxed_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v_x_188_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v_x_188_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v_x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 1);
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v_x_188_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v_x_188_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v_x_188_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 0);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg___boxed(lean_object* v_x_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(size_t v_sz_209_, size_t v_i_210_, lean_object* v_bs_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_210_, v_sz_209_);
if (v___x_212_ == 0)
{
return v_bs_211_;
}
else
{
lean_object* v_v_213_; lean_object* v_msg_214_; lean_object* v___x_215_; lean_object* v_bs_x27_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
v_v_213_ = lean_array_uget_borrowed(v_bs_211_, v_i_210_);
v_msg_214_ = lean_ctor_get(v_v_213_, 1);
lean_inc_ref(v_msg_214_);
v___x_215_ = lean_unsigned_to_nat(0u);
v_bs_x27_216_ = lean_array_uset(v_bs_211_, v_i_210_, v___x_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_210_, v___x_217_);
v___x_219_ = lean_array_uset(v_bs_x27_216_, v_i_210_, v_msg_214_);
v_i_210_ = v___x_218_;
v_bs_211_ = v___x_219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_221_, lean_object* v_i_222_, lean_object* v_bs_223_){
_start:
{
size_t v_sz_boxed_224_; size_t v_i_boxed_225_; lean_object* v_res_226_; 
v_sz_boxed_224_ = lean_unbox_usize(v_sz_221_);
lean_dec(v_sz_221_);
v_i_boxed_225_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_boxed_224_, v_i_boxed_225_, v_bs_223_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
lean_ctor_set(v___x_232_, 3, v___x_231_);
lean_ctor_set(v___x_232_, 4, v___x_230_);
lean_ctor_set(v___x_232_, 5, v___x_230_);
lean_ctor_set(v___x_232_, 6, v___x_230_);
lean_ctor_set(v___x_232_, 7, v___x_230_);
lean_ctor_set(v___x_232_, 8, v___x_230_);
lean_ctor_set(v___x_232_, 9, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(32u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4(void){
_start:
{
size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = ((size_t)5ULL);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_unsigned_to_nat(32u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3);
v___x_241_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_237_);
lean_ctor_set(v___x_241_, 3, v___x_237_);
lean_ctor_set_usize(v___x_241_, 4, v___x_236_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_box(1);
v___x_243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4);
v___x_244_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(lean_object* v_msgData_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; lean_object* v_env_251_; lean_object* v_options_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_250_ = lean_st_ref_get(v___y_248_);
v_env_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_env_251_);
lean_dec(v___x_250_);
v_options_252_ = lean_ctor_get(v___y_247_, 2);
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2);
v___x_254_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5);
lean_inc_ref(v_options_252_);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v_env_251_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v_options_252_);
v___x_256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_msgData_246_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___boxed(lean_object* v_msgData_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msgData_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object* v_oldTraces_263_, lean_object* v_data_264_, lean_object* v_ref_265_, lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_fileName_270_; lean_object* v_fileMap_271_; lean_object* v_options_272_; lean_object* v_currRecDepth_273_; lean_object* v_maxRecDepth_274_; lean_object* v_ref_275_; lean_object* v_currNamespace_276_; lean_object* v_openDecls_277_; lean_object* v_initHeartbeats_278_; lean_object* v_maxHeartbeats_279_; lean_object* v_quotContext_280_; lean_object* v_currMacroScope_281_; uint8_t v_diag_282_; lean_object* v_cancelTk_x3f_283_; uint8_t v_suppressElabErrors_284_; lean_object* v_inheritedTraceOptions_285_; lean_object* v___x_286_; lean_object* v_traceState_287_; lean_object* v_traces_288_; lean_object* v_ref_289_; lean_object* v___x_290_; lean_object* v___x_291_; size_t v_sz_292_; size_t v___x_293_; lean_object* v___x_294_; lean_object* v_msg_295_; lean_object* v___x_296_; lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_335_; 
v_fileName_270_ = lean_ctor_get(v___y_267_, 0);
v_fileMap_271_ = lean_ctor_get(v___y_267_, 1);
v_options_272_ = lean_ctor_get(v___y_267_, 2);
v_currRecDepth_273_ = lean_ctor_get(v___y_267_, 3);
v_maxRecDepth_274_ = lean_ctor_get(v___y_267_, 4);
v_ref_275_ = lean_ctor_get(v___y_267_, 5);
v_currNamespace_276_ = lean_ctor_get(v___y_267_, 6);
v_openDecls_277_ = lean_ctor_get(v___y_267_, 7);
v_initHeartbeats_278_ = lean_ctor_get(v___y_267_, 8);
v_maxHeartbeats_279_ = lean_ctor_get(v___y_267_, 9);
v_quotContext_280_ = lean_ctor_get(v___y_267_, 10);
v_currMacroScope_281_ = lean_ctor_get(v___y_267_, 11);
v_diag_282_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14);
v_cancelTk_x3f_283_ = lean_ctor_get(v___y_267_, 12);
v_suppressElabErrors_284_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_285_ = lean_ctor_get(v___y_267_, 13);
v___x_286_ = lean_st_ref_get(v___y_268_);
v_traceState_287_ = lean_ctor_get(v___x_286_, 4);
lean_inc_ref(v_traceState_287_);
lean_dec(v___x_286_);
v_traces_288_ = lean_ctor_get(v_traceState_287_, 0);
lean_inc_ref(v_traces_288_);
lean_dec_ref(v_traceState_287_);
v_ref_289_ = l_Lean_replaceRef(v_ref_265_, v_ref_275_);
lean_inc_ref(v_inheritedTraceOptions_285_);
lean_inc(v_cancelTk_x3f_283_);
lean_inc(v_currMacroScope_281_);
lean_inc(v_quotContext_280_);
lean_inc(v_maxHeartbeats_279_);
lean_inc(v_initHeartbeats_278_);
lean_inc(v_openDecls_277_);
lean_inc(v_currNamespace_276_);
lean_inc(v_maxRecDepth_274_);
lean_inc(v_currRecDepth_273_);
lean_inc_ref(v_options_272_);
lean_inc_ref(v_fileMap_271_);
lean_inc_ref(v_fileName_270_);
v___x_290_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_290_, 0, v_fileName_270_);
lean_ctor_set(v___x_290_, 1, v_fileMap_271_);
lean_ctor_set(v___x_290_, 2, v_options_272_);
lean_ctor_set(v___x_290_, 3, v_currRecDepth_273_);
lean_ctor_set(v___x_290_, 4, v_maxRecDepth_274_);
lean_ctor_set(v___x_290_, 5, v_ref_289_);
lean_ctor_set(v___x_290_, 6, v_currNamespace_276_);
lean_ctor_set(v___x_290_, 7, v_openDecls_277_);
lean_ctor_set(v___x_290_, 8, v_initHeartbeats_278_);
lean_ctor_set(v___x_290_, 9, v_maxHeartbeats_279_);
lean_ctor_set(v___x_290_, 10, v_quotContext_280_);
lean_ctor_set(v___x_290_, 11, v_currMacroScope_281_);
lean_ctor_set(v___x_290_, 12, v_cancelTk_x3f_283_);
lean_ctor_set(v___x_290_, 13, v_inheritedTraceOptions_285_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*14, v_diag_282_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*14 + 1, v_suppressElabErrors_284_);
v___x_291_ = l_Lean_PersistentArray_toArray___redArg(v_traces_288_);
lean_dec_ref(v_traces_288_);
v_sz_292_ = lean_array_size(v___x_291_);
v___x_293_ = ((size_t)0ULL);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_292_, v___x_293_, v___x_291_);
v_msg_295_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_295_, 0, v_data_264_);
lean_ctor_set(v_msg_295_, 1, v_msg_266_);
lean_ctor_set(v_msg_295_, 2, v___x_294_);
v___x_296_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msg_295_, v___x_290_, v___y_268_);
lean_dec_ref(v___x_290_);
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_335_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_335_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_335_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v_traceState_302_; lean_object* v_env_303_; lean_object* v_nextMacroScope_304_; lean_object* v_ngen_305_; lean_object* v_auxDeclNGen_306_; lean_object* v_cache_307_; lean_object* v_messages_308_; lean_object* v_infoState_309_; lean_object* v_snapshotTasks_310_; lean_object* v_newDecls_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_334_; 
v___x_301_ = lean_st_ref_take(v___y_268_);
v_traceState_302_ = lean_ctor_get(v___x_301_, 4);
v_env_303_ = lean_ctor_get(v___x_301_, 0);
v_nextMacroScope_304_ = lean_ctor_get(v___x_301_, 1);
v_ngen_305_ = lean_ctor_get(v___x_301_, 2);
v_auxDeclNGen_306_ = lean_ctor_get(v___x_301_, 3);
v_cache_307_ = lean_ctor_get(v___x_301_, 5);
v_messages_308_ = lean_ctor_get(v___x_301_, 6);
v_infoState_309_ = lean_ctor_get(v___x_301_, 7);
v_snapshotTasks_310_ = lean_ctor_get(v___x_301_, 8);
v_newDecls_311_ = lean_ctor_get(v___x_301_, 9);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_334_ == 0)
{
v___x_313_ = v___x_301_;
v_isShared_314_ = v_isSharedCheck_334_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_newDecls_311_);
lean_inc(v_snapshotTasks_310_);
lean_inc(v_infoState_309_);
lean_inc(v_messages_308_);
lean_inc(v_cache_307_);
lean_inc(v_traceState_302_);
lean_inc(v_auxDeclNGen_306_);
lean_inc(v_ngen_305_);
lean_inc(v_nextMacroScope_304_);
lean_inc(v_env_303_);
lean_dec(v___x_301_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_334_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_332_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_302_, sizeof(void*)*1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_traceState_302_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v_traceState_302_, 0);
lean_dec(v_unused_333_);
v___x_317_ = v_traceState_302_;
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_traceState_302_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_ref_265_);
lean_ctor_set(v___x_319_, 1, v_a_297_);
v___x_320_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_263_, v___x_319_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_320_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_320_);
lean_ctor_set_uint64(v_reuseFailAlloc_331_, sizeof(void*)*1, v_tid_315_);
v___x_322_ = v_reuseFailAlloc_331_;
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
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_env_303_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_nextMacroScope_304_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ngen_305_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_auxDeclNGen_306_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v_cache_307_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_messages_308_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_infoState_309_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_snapshotTasks_310_);
lean_ctor_set(v_reuseFailAlloc_330_, 9, v_newDecls_311_);
v___x_324_ = v_reuseFailAlloc_330_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_st_ref_set(v___y_268_, v___x_324_);
v___x_326_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_326_);
v___x_328_ = v___x_299_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object* v_oldTraces_336_, lean_object* v_data_337_, lean_object* v_ref_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_336_, v_data_337_, v_ref_338_, v_msg_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object* v_e_344_){
_start:
{
if (lean_obj_tag(v_e_344_) == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 2;
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object* v_e_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_e_347_);
lean_dec_ref(v_e_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2(void){
_start:
{
lean_object* v___x_353_; double v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_float_of_nat(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5(void){
_start:
{
lean_object* v___x_358_; double v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1000u);
v___x_359_ = lean_float_of_nat(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(lean_object* v_cls_360_, uint8_t v_collapsed_361_, lean_object* v_tag_362_, lean_object* v_opts_363_, uint8_t v_clsEnabled_364_, lean_object* v_oldTraces_365_, lean_object* v_msg_366_, lean_object* v_resStartStop_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_463_; 
v_fst_371_ = lean_ctor_get(v_resStartStop_367_, 0);
v_snd_372_ = lean_ctor_get(v_resStartStop_367_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_resStartStop_367_);
if (v_isSharedCheck_463_ == 0)
{
v___x_374_ = v_resStartStop_367_;
v_isShared_375_ = v_isSharedCheck_463_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_snd_372_);
lean_inc(v_fst_371_);
lean_dec(v_resStartStop_367_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_463_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v_data_379_; lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_462_; 
v_fst_382_ = lean_ctor_get(v_snd_372_, 0);
v_snd_383_ = lean_ctor_get(v_snd_372_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_snd_372_);
if (v_isSharedCheck_462_ == 0)
{
v___x_385_ = v_snd_372_;
v_isShared_386_ = v_isSharedCheck_462_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snd_383_);
lean_inc(v_fst_382_);
lean_dec(v_snd_372_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_462_;
goto v_resetjp_384_;
}
v___jp_376_:
{
lean_object* v___x_380_; 
lean_inc(v___y_377_);
v___x_380_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_365_, v_data_379_, v___y_377_, v___y_378_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_381_; 
lean_dec_ref(v___x_380_);
v___x_381_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_371_);
return v___x_381_;
}
else
{
lean_dec(v_fst_371_);
return v___x_380_;
}
}
v_resetjp_384_:
{
lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___y_390_; lean_object* v_a_391_; uint8_t v___y_415_; double v___y_447_; 
v___x_387_ = l_Lean_trace_profiler;
v___x_388_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_363_, v___x_387_);
if (v___x_388_ == 0)
{
v___y_415_ = v___x_388_;
goto v___jp_414_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = l_Lean_trace_profiler_useHeartbeats;
v___x_453_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_363_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; double v___x_456_; double v___x_457_; double v___x_458_; 
v___x_454_ = l_Lean_trace_profiler_threshold;
v___x_455_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_363_, v___x_454_);
v___x_456_ = lean_float_of_nat(v___x_455_);
v___x_457_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5);
v___x_458_ = lean_float_div(v___x_456_, v___x_457_);
v___y_447_ = v___x_458_;
goto v___jp_446_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; double v___x_461_; 
v___x_459_ = l_Lean_trace_profiler_threshold;
v___x_460_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_363_, v___x_459_);
v___x_461_ = lean_float_of_nat(v___x_460_);
v___y_447_ = v___x_461_;
goto v___jp_446_;
}
}
v___jp_389_:
{
uint8_t v_result_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v_result_392_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_fst_371_);
v___x_393_ = l_Lean_TraceResult_toEmoji(v_result_392_);
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
v___x_395_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 7);
lean_ctor_set(v___x_385_, 1, v___x_395_);
lean_ctor_set(v___x_385_, 0, v___x_394_);
v___x_397_ = v___x_385_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_408_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v_m_399_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 7);
lean_ctor_set(v___x_374_, 1, v_a_391_);
lean_ctor_set(v___x_374_, 0, v___x_397_);
v_m_399_ = v___x_374_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_391_);
v_m_399_ = v_reuseFailAlloc_407_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; double v___x_402_; lean_object* v_data_403_; 
v___x_400_ = lean_box(v_result_392_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2);
lean_inc_ref(v_tag_362_);
lean_inc_ref(v___x_401_);
lean_inc(v_cls_360_);
v_data_403_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_403_, 0, v_cls_360_);
lean_ctor_set(v_data_403_, 1, v___x_401_);
lean_ctor_set(v_data_403_, 2, v_tag_362_);
lean_ctor_set_float(v_data_403_, sizeof(void*)*3, v___x_402_);
lean_ctor_set_float(v_data_403_, sizeof(void*)*3 + 8, v___x_402_);
lean_ctor_set_uint8(v_data_403_, sizeof(void*)*3 + 16, v_collapsed_361_);
if (v___x_388_ == 0)
{
lean_dec_ref(v___x_401_);
lean_dec(v_snd_383_);
lean_dec(v_fst_382_);
lean_dec_ref(v_tag_362_);
lean_dec(v_cls_360_);
v___y_377_ = v___y_390_;
v___y_378_ = v_m_399_;
v_data_379_ = v_data_403_;
goto v___jp_376_;
}
else
{
lean_object* v_data_404_; double v___x_405_; double v___x_406_; 
lean_dec_ref(v_data_403_);
v_data_404_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_404_, 0, v_cls_360_);
lean_ctor_set(v_data_404_, 1, v___x_401_);
lean_ctor_set(v_data_404_, 2, v_tag_362_);
v___x_405_ = lean_unbox_float(v_fst_382_);
lean_dec(v_fst_382_);
lean_ctor_set_float(v_data_404_, sizeof(void*)*3, v___x_405_);
v___x_406_ = lean_unbox_float(v_snd_383_);
lean_dec(v_snd_383_);
lean_ctor_set_float(v_data_404_, sizeof(void*)*3 + 8, v___x_406_);
lean_ctor_set_uint8(v_data_404_, sizeof(void*)*3 + 16, v_collapsed_361_);
v___y_377_ = v___y_390_;
v___y_378_ = v_m_399_;
v_data_379_ = v_data_404_;
goto v___jp_376_;
}
}
}
}
v___jp_409_:
{
lean_object* v_ref_410_; lean_object* v___x_411_; 
v_ref_410_ = lean_ctor_get(v___y_368_, 5);
lean_inc(v___y_369_);
lean_inc_ref(v___y_368_);
lean_inc(v_fst_371_);
v___x_411_ = lean_apply_4(v_msg_366_, v_fst_371_, v___y_368_, v___y_369_, lean_box(0));
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v___y_390_ = v_ref_410_;
v_a_391_ = v_a_412_;
goto v___jp_389_;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v___x_411_);
v___x_413_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4);
v___y_390_ = v_ref_410_;
v_a_391_ = v___x_413_;
goto v___jp_389_;
}
}
v___jp_414_:
{
if (v_clsEnabled_364_ == 0)
{
if (v___y_415_ == 0)
{
lean_object* v___x_416_; lean_object* v_traceState_417_; lean_object* v_env_418_; lean_object* v_nextMacroScope_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_cache_422_; lean_object* v_messages_423_; lean_object* v_infoState_424_; lean_object* v_snapshotTasks_425_; lean_object* v_newDecls_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_dec(v_fst_382_);
lean_del_object(v___x_374_);
lean_dec_ref(v_msg_366_);
lean_dec_ref(v_tag_362_);
lean_dec(v_cls_360_);
v___x_416_ = lean_st_ref_take(v___y_369_);
v_traceState_417_ = lean_ctor_get(v___x_416_, 4);
v_env_418_ = lean_ctor_get(v___x_416_, 0);
v_nextMacroScope_419_ = lean_ctor_get(v___x_416_, 1);
v_ngen_420_ = lean_ctor_get(v___x_416_, 2);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_416_, 3);
v_cache_422_ = lean_ctor_get(v___x_416_, 5);
v_messages_423_ = lean_ctor_get(v___x_416_, 6);
v_infoState_424_ = lean_ctor_get(v___x_416_, 7);
v_snapshotTasks_425_ = lean_ctor_get(v___x_416_, 8);
v_newDecls_426_ = lean_ctor_get(v___x_416_, 9);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_428_ = v___x_416_;
v_isShared_429_ = v_isSharedCheck_445_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_newDecls_426_);
lean_inc(v_snapshotTasks_425_);
lean_inc(v_infoState_424_);
lean_inc(v_messages_423_);
lean_inc(v_cache_422_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_nextMacroScope_419_);
lean_inc(v_env_418_);
lean_dec(v___x_416_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_445_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint64_t v_tid_430_; lean_object* v_traces_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_444_; 
v_tid_430_ = lean_ctor_get_uint64(v_traceState_417_, sizeof(void*)*1);
v_traces_431_ = lean_ctor_get(v_traceState_417_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_traceState_417_);
if (v_isSharedCheck_444_ == 0)
{
v___x_433_ = v_traceState_417_;
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_traces_431_);
lean_dec(v_traceState_417_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_365_, v_traces_431_);
lean_dec_ref(v_traces_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_435_);
lean_ctor_set_uint64(v_reuseFailAlloc_443_, sizeof(void*)*1, v_tid_430_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v___x_437_);
v___x_439_ = v___x_428_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_env_418_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_nextMacroScope_419_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 5, v_cache_422_);
lean_ctor_set(v_reuseFailAlloc_442_, 6, v_messages_423_);
lean_ctor_set(v_reuseFailAlloc_442_, 7, v_infoState_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 8, v_snapshotTasks_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 9, v_newDecls_426_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_st_ref_set(v___y_369_, v___x_439_);
v___x_441_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_371_);
return v___x_441_;
}
}
}
}
}
else
{
goto v___jp_409_;
}
}
else
{
goto v___jp_409_;
}
}
v___jp_446_:
{
double v___x_448_; double v___x_449_; double v___x_450_; uint8_t v___x_451_; 
v___x_448_ = lean_unbox_float(v_snd_383_);
v___x_449_ = lean_unbox_float(v_fst_382_);
v___x_450_ = lean_float_sub(v___x_448_, v___x_449_);
v___x_451_ = lean_float_decLt(v___y_447_, v___x_450_);
v___y_415_ = v___x_451_;
goto v___jp_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_cls_464_, lean_object* v_collapsed_465_, lean_object* v_tag_466_, lean_object* v_opts_467_, lean_object* v_clsEnabled_468_, lean_object* v_oldTraces_469_, lean_object* v_msg_470_, lean_object* v_resStartStop_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
uint8_t v_collapsed_boxed_475_; uint8_t v_clsEnabled_boxed_476_; lean_object* v_res_477_; 
v_collapsed_boxed_475_ = lean_unbox(v_collapsed_465_);
v_clsEnabled_boxed_476_ = lean_unbox(v_clsEnabled_468_);
v_res_477_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v_cls_464_, v_collapsed_boxed_475_, v_tag_466_, v_opts_467_, v_clsEnabled_boxed_476_, v_oldTraces_469_, v_msg_470_, v_resStartStop_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_opts_467_);
return v_res_477_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_478_; double v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1000000000u);
v___x_479_ = lean_float_of_nat(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__3(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_485_, uint8_t v___x_486_, lean_object* v___x_487_, lean_object* v___f_488_, lean_object* v_declNames_489_, lean_object* v___x_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v_fileName_495_; lean_object* v_fileMap_496_; lean_object* v_options_497_; lean_object* v_currRecDepth_498_; lean_object* v_ref_499_; lean_object* v_currNamespace_500_; lean_object* v_openDecls_501_; lean_object* v_initHeartbeats_502_; lean_object* v_maxHeartbeats_503_; lean_object* v_quotContext_504_; lean_object* v_currMacroScope_505_; lean_object* v_cancelTk_x3f_506_; uint8_t v_suppressElabErrors_507_; lean_object* v_inheritedTraceOptions_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_647_; 
v___x_494_ = lean_st_ref_get(v___y_492_);
v_fileName_495_ = lean_ctor_get(v___y_491_, 0);
v_fileMap_496_ = lean_ctor_get(v___y_491_, 1);
v_options_497_ = lean_ctor_get(v___y_491_, 2);
v_currRecDepth_498_ = lean_ctor_get(v___y_491_, 3);
v_ref_499_ = lean_ctor_get(v___y_491_, 5);
v_currNamespace_500_ = lean_ctor_get(v___y_491_, 6);
v_openDecls_501_ = lean_ctor_get(v___y_491_, 7);
v_initHeartbeats_502_ = lean_ctor_get(v___y_491_, 8);
v_maxHeartbeats_503_ = lean_ctor_get(v___y_491_, 9);
v_quotContext_504_ = lean_ctor_get(v___y_491_, 10);
v_currMacroScope_505_ = lean_ctor_get(v___y_491_, 11);
v_cancelTk_x3f_506_ = lean_ctor_get(v___y_491_, 12);
v_suppressElabErrors_507_ = lean_ctor_get_uint8(v___y_491_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_508_ = lean_ctor_get(v___y_491_, 13);
v_isSharedCheck_647_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___y_491_, 4);
lean_dec(v_unused_648_);
v___x_510_ = v___y_491_;
v_isShared_511_ = v_isSharedCheck_647_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_inheritedTraceOptions_508_);
lean_inc(v_cancelTk_x3f_506_);
lean_inc(v_currMacroScope_505_);
lean_inc(v_quotContext_504_);
lean_inc(v_maxHeartbeats_503_);
lean_inc(v_initHeartbeats_502_);
lean_inc(v_openDecls_501_);
lean_inc(v_currNamespace_500_);
lean_inc(v_ref_499_);
lean_inc(v_currRecDepth_498_);
lean_inc(v_options_497_);
lean_inc(v_fileMap_496_);
lean_inc(v_fileName_495_);
lean_dec(v___y_491_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_647_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_env_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v_a_522_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v_a_540_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v_fileName_596_; lean_object* v_fileMap_597_; lean_object* v_currRecDepth_598_; lean_object* v_ref_599_; lean_object* v_currNamespace_600_; lean_object* v_openDecls_601_; lean_object* v_initHeartbeats_602_; lean_object* v_maxHeartbeats_603_; lean_object* v_quotContext_604_; lean_object* v_currMacroScope_605_; lean_object* v_cancelTk_x3f_606_; uint8_t v_suppressElabErrors_607_; lean_object* v_inheritedTraceOptions_608_; lean_object* v___y_609_; uint8_t v___y_624_; uint8_t v___x_646_; 
v_env_512_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref(v_env_512_);
lean_dec(v___x_494_);
v___x_513_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_514_ = 0;
v___x_515_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_options_497_, v___x_513_, v___x_514_);
v___x_593_ = l_Lean_diagnostics;
v___x_594_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_515_, v___x_593_);
v___x_646_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_512_);
lean_dec_ref(v_env_512_);
if (v___x_646_ == 0)
{
if (v___x_594_ == 0)
{
v_fileName_596_ = v_fileName_495_;
v_fileMap_597_ = v_fileMap_496_;
v_currRecDepth_598_ = v_currRecDepth_498_;
v_ref_599_ = v_ref_499_;
v_currNamespace_600_ = v_currNamespace_500_;
v_openDecls_601_ = v_openDecls_501_;
v_initHeartbeats_602_ = v_initHeartbeats_502_;
v_maxHeartbeats_603_ = v_maxHeartbeats_503_;
v_quotContext_604_ = v_quotContext_504_;
v_currMacroScope_605_ = v_currMacroScope_505_;
v_cancelTk_x3f_606_ = v_cancelTk_x3f_506_;
v_suppressElabErrors_607_ = v_suppressElabErrors_507_;
v_inheritedTraceOptions_608_ = v_inheritedTraceOptions_508_;
v___y_609_ = v___y_492_;
goto v___jp_595_;
}
else
{
v___y_624_ = v___x_646_;
goto v___jp_623_;
}
}
else
{
v___y_624_ = v___x_594_;
goto v___jp_623_;
}
v___jp_516_:
{
lean_object* v___x_523_; double v___x_524_; double v___x_525_; double v___x_526_; double v___x_527_; double v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_523_ = lean_io_mono_nanos_now();
v___x_524_ = lean_float_of_nat(v___y_519_);
v___x_525_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_526_ = lean_float_div(v___x_524_, v___x_525_);
v___x_527_ = lean_float_of_nat(v___x_523_);
v___x_528_ = lean_float_div(v___x_527_, v___x_525_);
v___x_529_ = lean_box_float(v___x_526_);
v___x_530_ = lean_box_float(v___x_528_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_522_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_485_, v___x_486_, v___x_487_, v___x_515_, v___y_521_, v___y_520_, v___f_488_, v___x_532_, v___y_517_, v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___x_515_);
return v___x_533_;
}
v___jp_534_:
{
lean_object* v___x_541_; double v___x_542_; double v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_541_ = lean_io_get_num_heartbeats();
v___x_542_ = lean_float_of_nat(v___y_535_);
v___x_543_ = lean_float_of_nat(v___x_541_);
v___x_544_ = lean_box_float(v___x_542_);
v___x_545_ = lean_box_float(v___x_543_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_540_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_485_, v___x_486_, v___x_487_, v___x_515_, v___y_539_, v___y_538_, v___f_488_, v___x_547_, v___y_536_, v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v___x_515_);
return v___x_548_;
}
v___jp_549_:
{
lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_553_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_551_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = l_Lean_trace_profiler_useHeartbeats;
v___x_556_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_515_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_io_mono_nanos_now();
v___x_558_ = l_Lean_Compiler_LCNF_main(v_declNames_489_, v___x_490_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
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
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_517_ = v___y_550_;
v___y_518_ = v___y_551_;
v___y_519_ = v___x_557_;
v___y_520_ = v_a_554_;
v___y_521_ = v___y_552_;
v_a_522_ = v___x_564_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_558_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_558_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 0);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_517_ = v___y_550_;
v___y_518_ = v___y_551_;
v___y_519_ = v___x_557_;
v___y_520_ = v_a_554_;
v___y_521_ = v___y_552_;
v_a_522_ = v___x_572_;
goto v___jp_516_;
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_io_get_num_heartbeats();
v___x_576_ = l_Lean_Compiler_LCNF_main(v_declNames_489_, v___x_490_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 1);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_535_ = v___x_575_;
v___y_536_ = v___y_550_;
v___y_537_ = v___y_551_;
v___y_538_ = v_a_554_;
v___y_539_ = v___y_552_;
v_a_540_ = v___x_582_;
goto v___jp_534_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_576_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 0);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v___y_535_ = v___x_575_;
v___y_536_ = v___y_550_;
v___y_537_ = v___y_551_;
v___y_538_ = v_a_554_;
v___y_539_ = v___y_552_;
v_a_540_ = v___x_590_;
goto v___jp_534_;
}
}
}
}
}
v___jp_595_:
{
uint8_t v_hasTrace_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_hasTrace_610_ = lean_ctor_get_uint8(v___x_515_, sizeof(void*)*1);
v___x_611_ = l_Lean_maxRecDepth;
v___x_612_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___x_515_, v___x_611_);
lean_inc_ref(v_inheritedTraceOptions_608_);
lean_inc_ref(v___x_515_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 13, v_inheritedTraceOptions_608_);
lean_ctor_set(v___x_510_, 12, v_cancelTk_x3f_606_);
lean_ctor_set(v___x_510_, 11, v_currMacroScope_605_);
lean_ctor_set(v___x_510_, 10, v_quotContext_604_);
lean_ctor_set(v___x_510_, 9, v_maxHeartbeats_603_);
lean_ctor_set(v___x_510_, 8, v_initHeartbeats_602_);
lean_ctor_set(v___x_510_, 7, v_openDecls_601_);
lean_ctor_set(v___x_510_, 6, v_currNamespace_600_);
lean_ctor_set(v___x_510_, 5, v_ref_599_);
lean_ctor_set(v___x_510_, 4, v___x_612_);
lean_ctor_set(v___x_510_, 3, v_currRecDepth_598_);
lean_ctor_set(v___x_510_, 2, v___x_515_);
lean_ctor_set(v___x_510_, 1, v_fileMap_597_);
lean_ctor_set(v___x_510_, 0, v_fileName_596_);
v___x_614_ = v___x_510_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_fileName_596_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_fileMap_597_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_currRecDepth_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_ref_599_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_currNamespace_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_openDecls_601_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_initHeartbeats_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 9, v_maxHeartbeats_603_);
lean_ctor_set(v_reuseFailAlloc_622_, 10, v_quotContext_604_);
lean_ctor_set(v_reuseFailAlloc_622_, 11, v_currMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 12, v_cancelTk_x3f_606_);
lean_ctor_set(v_reuseFailAlloc_622_, 13, v_inheritedTraceOptions_608_);
v___x_614_ = v_reuseFailAlloc_622_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*14, v___x_594_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*14 + 1, v_suppressElabErrors_607_);
if (v_hasTrace_610_ == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v_inheritedTraceOptions_608_);
lean_dec_ref(v___x_515_);
lean_dec_ref(v___f_488_);
lean_dec_ref(v___x_487_);
lean_dec(v___x_485_);
v___x_615_ = l_Lean_Compiler_LCNF_main(v_declNames_489_, v___x_490_, v___x_614_, v___y_609_);
lean_dec_ref(v___x_614_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
lean_inc(v___x_485_);
v___x_617_ = l_Lean_Name_append(v___x_616_, v___x_485_);
v___x_618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_608_, v___x_515_, v___x_617_);
lean_dec(v___x_617_);
lean_dec_ref(v_inheritedTraceOptions_608_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = l_Lean_trace_profiler;
v___x_620_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_515_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec_ref(v___x_515_);
lean_dec_ref(v___f_488_);
lean_dec_ref(v___x_487_);
lean_dec(v___x_485_);
v___x_621_ = l_Lean_Compiler_LCNF_main(v_declNames_489_, v___x_490_, v___x_614_, v___y_609_);
lean_dec_ref(v___x_614_);
return v___x_621_;
}
else
{
v___y_550_ = v___x_614_;
v___y_551_ = v___y_609_;
v___y_552_ = v___x_618_;
goto v___jp_549_;
}
}
else
{
v___y_550_ = v___x_614_;
v___y_551_ = v___y_609_;
v___y_552_ = v___x_618_;
goto v___jp_549_;
}
}
}
}
v___jp_623_:
{
if (v___y_624_ == 0)
{
lean_object* v___x_625_; lean_object* v_env_626_; lean_object* v_nextMacroScope_627_; lean_object* v_ngen_628_; lean_object* v_auxDeclNGen_629_; lean_object* v_traceState_630_; lean_object* v_messages_631_; lean_object* v_infoState_632_; lean_object* v_snapshotTasks_633_; lean_object* v_newDecls_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_644_; 
v___x_625_ = lean_st_ref_take(v___y_492_);
v_env_626_ = lean_ctor_get(v___x_625_, 0);
v_nextMacroScope_627_ = lean_ctor_get(v___x_625_, 1);
v_ngen_628_ = lean_ctor_get(v___x_625_, 2);
v_auxDeclNGen_629_ = lean_ctor_get(v___x_625_, 3);
v_traceState_630_ = lean_ctor_get(v___x_625_, 4);
v_messages_631_ = lean_ctor_get(v___x_625_, 6);
v_infoState_632_ = lean_ctor_get(v___x_625_, 7);
v_snapshotTasks_633_ = lean_ctor_get(v___x_625_, 8);
v_newDecls_634_ = lean_ctor_get(v___x_625_, 9);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_625_, 5);
lean_dec(v_unused_645_);
v___x_636_ = v___x_625_;
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_newDecls_634_);
lean_inc(v_snapshotTasks_633_);
lean_inc(v_infoState_632_);
lean_inc(v_messages_631_);
lean_inc(v_traceState_630_);
lean_inc(v_auxDeclNGen_629_);
lean_inc(v_ngen_628_);
lean_inc(v_nextMacroScope_627_);
lean_inc(v_env_626_);
lean_dec(v___x_625_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = l_Lean_Kernel_enableDiag(v_env_626_, v___x_594_);
v___x_639_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__3, &l_Lean_Compiler_compile___lam__1___closed__3_once, _init_l_Lean_Compiler_compile___lam__1___closed__3);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 5, v___x_639_);
lean_ctor_set(v___x_636_, 0, v___x_638_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_nextMacroScope_627_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_ngen_628_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_auxDeclNGen_629_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_traceState_630_);
lean_ctor_set(v_reuseFailAlloc_643_, 5, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_643_, 6, v_messages_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 7, v_infoState_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 8, v_snapshotTasks_633_);
lean_ctor_set(v_reuseFailAlloc_643_, 9, v_newDecls_634_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_st_ref_set(v___y_492_, v___x_641_);
v_fileName_596_ = v_fileName_495_;
v_fileMap_597_ = v_fileMap_496_;
v_currRecDepth_598_ = v_currRecDepth_498_;
v_ref_599_ = v_ref_499_;
v_currNamespace_600_ = v_currNamespace_500_;
v_openDecls_601_ = v_openDecls_501_;
v_initHeartbeats_602_ = v_initHeartbeats_502_;
v_maxHeartbeats_603_ = v_maxHeartbeats_503_;
v_quotContext_604_ = v_quotContext_504_;
v_currMacroScope_605_ = v_currMacroScope_505_;
v_cancelTk_x3f_606_ = v_cancelTk_x3f_506_;
v_suppressElabErrors_607_ = v_suppressElabErrors_507_;
v_inheritedTraceOptions_608_ = v_inheritedTraceOptions_508_;
v___y_609_ = v___y_492_;
goto v___jp_595_;
}
}
}
else
{
v_fileName_596_ = v_fileName_495_;
v_fileMap_597_ = v_fileMap_496_;
v_currRecDepth_598_ = v_currRecDepth_498_;
v_ref_599_ = v_ref_499_;
v_currNamespace_600_ = v_currNamespace_500_;
v_openDecls_601_ = v_openDecls_501_;
v_initHeartbeats_602_ = v_initHeartbeats_502_;
v_maxHeartbeats_603_ = v_maxHeartbeats_503_;
v_quotContext_604_ = v_quotContext_504_;
v_currMacroScope_605_ = v_currMacroScope_505_;
v_cancelTk_x3f_606_ = v_cancelTk_x3f_506_;
v_suppressElabErrors_607_ = v_suppressElabErrors_507_;
v_inheritedTraceOptions_608_ = v_inheritedTraceOptions_508_;
v___y_609_ = v___y_492_;
goto v___jp_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v___f_652_, lean_object* v_declNames_653_, lean_object* v___x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_7076__boxed_658_; lean_object* v_res_659_; 
v___x_7076__boxed_658_ = lean_unbox(v___x_650_);
v_res_659_ = l_Lean_Compiler_compile___lam__1(v___x_649_, v___x_7076__boxed_658_, v___x_651_, v___f_652_, v_declNames_653_, v___x_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_options_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_options_669_ = lean_ctor_get(v_a_666_, 2);
lean_inc_ref(v_declNames_665_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_670_, 0, v_declNames_665_);
v___x_671_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_672_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_673_ = l_Lean_Options_empty;
v___x_674_ = 1;
v___x_675_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_676_ = lean_box(v___x_674_);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_677_, 0, v___x_672_);
lean_closure_set(v___f_677_, 1, v___x_676_);
lean_closure_set(v___f_677_, 2, v___x_675_);
lean_closure_set(v___f_677_, 3, v___f_670_);
lean_closure_set(v___f_677_, 4, v_declNames_665_);
lean_closure_set(v___f_677_, 5, v___x_673_);
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_671_, v_options_669_, v___f_677_, v___x_678_, v_a_666_, v_a_667_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Compiler_compile(v_declNames_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_00_u03b1_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_00_u03b1_691_, v_x_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_758_ = 0;
v___x_759_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_760_ = l_Lean_registerTraceClass(v___x_757_, v___x_758_, v___x_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref(v___x_760_);
v___x_761_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_762_ = l_Lean_registerTraceClass(v___x_761_, v___x_758_, v___x_759_);
return v___x_762_;
}
else
{
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_764_;
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

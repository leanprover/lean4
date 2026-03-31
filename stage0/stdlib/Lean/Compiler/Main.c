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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
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
lean_object* v___x_37_; lean_object* v_traceState_38_; lean_object* v_traces_39_; lean_object* v___x_40_; lean_object* v_traceState_41_; lean_object* v_env_42_; lean_object* v_nextMacroScope_43_; lean_object* v_ngen_44_; lean_object* v_auxDeclNGen_45_; lean_object* v_cache_46_; lean_object* v_messages_47_; lean_object* v_infoState_48_; lean_object* v_snapshotTasks_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_68_; 
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
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_68_ == 0)
{
v___x_51_ = v___x_40_;
v_isShared_52_ = v_isSharedCheck_68_;
goto v_resetjp_50_;
}
else
{
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
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_68_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint64_t v_tid_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_66_; 
v_tid_53_ = lean_ctor_get_uint64(v_traceState_41_, sizeof(void*)*1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_traceState_41_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v_traceState_41_, 0);
lean_dec(v_unused_67_);
v___x_55_ = v_traceState_41_;
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
else
{
lean_dec(v_traceState_41_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_57_);
lean_ctor_set_uint64(v_reuseFailAlloc_65_, sizeof(void*)*1, v_tid_53_);
v___x_59_ = v_reuseFailAlloc_65_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_61_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 4, v___x_59_);
v___x_61_ = v___x_51_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_env_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_nextMacroScope_43_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_ngen_44_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_auxDeclNGen_45_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_cache_46_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v_messages_47_);
lean_ctor_set(v_reuseFailAlloc_64_, 7, v_infoState_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 8, v_snapshotTasks_49_);
v___x_61_ = v_reuseFailAlloc_64_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_st_ref_set(v___y_35_, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_traces_39_);
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___boxed(lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_69_);
lean_dec(v___y_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(lean_object* v_category_80_, lean_object* v_opts_81_, lean_object* v_act_82_, lean_object* v_decl_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_87_ = lean_apply_2(v_act_82_, v___y_84_, v___y_85_);
v___x_88_ = l_Lean_profileitIOUnsafe___redArg(v_category_80_, v_opts_81_, v___x_87_, v_decl_83_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg___boxed(lean_object* v_category_89_, lean_object* v_opts_90_, lean_object* v_act_91_, lean_object* v_decl_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_89_, v_opts_90_, v_act_91_, v_decl_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_opts_90_);
lean_dec_ref(v_category_89_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(lean_object* v_00_u03b1_97_, lean_object* v_category_98_, lean_object* v_opts_99_, lean_object* v_act_100_, lean_object* v_decl_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_98_, v_opts_99_, v_act_100_, v_decl_101_, v___y_102_, v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___boxed(lean_object* v_00_u03b1_106_, lean_object* v_category_107_, lean_object* v_opts_108_, lean_object* v_act_109_, lean_object* v_decl_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(v_00_u03b1_106_, v_category_107_, v_opts_108_, v_act_109_, v_decl_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec_ref(v_opts_108_);
lean_dec_ref(v_category_107_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
if (lean_obj_tag(v_a_115_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = l_List_reverse___redArg(v_a_116_);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
v_head_118_ = lean_ctor_get(v_a_115_, 0);
v_tail_119_ = lean_ctor_get(v_a_115_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_128_ == 0)
{
v___x_121_ = v_a_115_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_tail_119_);
lean_inc(v_head_118_);
lean_dec(v_a_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = l_Lean_MessageData_ofName(v_head_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_a_116_);
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_a_116_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
v_a_115_ = v_tail_119_;
v_a_116_ = v___x_125_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Compiler_compile___lam__0___closed__0));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object* v_declNames_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = lean_obj_once(&l_Lean_Compiler_compile___lam__0___closed__1, &l_Lean_Compiler_compile___lam__0___closed__1_once, _init_l_Lean_Compiler_compile___lam__0___closed__1);
v___x_138_ = lean_array_to_list(v_declNames_132_);
v___x_139_ = lean_box(0);
v___x_140_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_138_, v___x_139_);
v___x_141_ = l_Lean_MessageData_ofList(v___x_140_);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_137_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* v_declNames_144_, lean_object* v_x_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Compiler_compile___lam__0(v_declNames_144_, v_x_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec_ref(v_x_145_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(lean_object* v_o_153_, lean_object* v_k_154_, uint8_t v_v_155_){
_start:
{
lean_object* v_map_156_; uint8_t v_hasTrace_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_171_; 
v_map_156_ = lean_ctor_get(v_o_153_, 0);
v_hasTrace_157_ = lean_ctor_get_uint8(v_o_153_, sizeof(void*)*1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_o_153_);
if (v_isSharedCheck_171_ == 0)
{
v___x_159_ = v_o_153_;
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_map_156_);
lean_dec(v_o_153_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_161_, 0, v_v_155_);
lean_inc(v_k_154_);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_154_, v___x_161_, v_map_156_);
if (v_hasTrace_157_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
v___x_164_ = l_Lean_Name_isPrefixOf(v___x_163_, v_k_154_);
lean_dec(v_k_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_162_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_162_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_164_);
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
lean_dec(v_k_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_162_);
v___x_169_ = v___x_159_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*1, v_hasTrace_157_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(lean_object* v_o_172_, lean_object* v_k_173_, lean_object* v_v_174_){
_start:
{
uint8_t v_v_boxed_175_; lean_object* v_res_176_; 
v_v_boxed_175_ = lean_unbox(v_v_174_);
v_res_176_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_o_172_, v_k_173_, v_v_boxed_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(lean_object* v_opts_177_, lean_object* v_opt_178_, uint8_t v_val_179_){
_start:
{
lean_object* v_name_180_; lean_object* v___x_181_; 
v_name_180_ = lean_ctor_get(v_opt_178_, 0);
lean_inc(v_name_180_);
lean_dec_ref(v_opt_178_);
v___x_181_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(v_opts_177_, v_name_180_, v_val_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(lean_object* v_opts_182_, lean_object* v_opt_183_, lean_object* v_val_184_){
_start:
{
uint8_t v_val_boxed_185_; lean_object* v_res_186_; 
v_val_boxed_185_ = lean_unbox(v_val_184_);
v_res_186_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_opts_182_, v_opt_183_, v_val_boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v_x_187_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v_x_187_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v_x_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 1);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v_x_187_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v_x_187_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v_x_187_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 0);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg___boxed(lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(size_t v_sz_208_, size_t v_i_209_, lean_object* v_bs_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_lt(v_i_209_, v_sz_208_);
if (v___x_211_ == 0)
{
return v_bs_210_;
}
else
{
lean_object* v_v_212_; lean_object* v_msg_213_; lean_object* v___x_214_; lean_object* v_bs_x27_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; 
v_v_212_ = lean_array_uget_borrowed(v_bs_210_, v_i_209_);
v_msg_213_ = lean_ctor_get(v_v_212_, 1);
lean_inc_ref(v_msg_213_);
v___x_214_ = lean_unsigned_to_nat(0u);
v_bs_x27_215_ = lean_array_uset(v_bs_210_, v_i_209_, v___x_214_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_i_209_, v___x_216_);
v___x_218_ = lean_array_uset(v_bs_x27_215_, v_i_209_, v_msg_213_);
v_i_209_ = v___x_217_;
v_bs_210_ = v___x_218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_220_, lean_object* v_i_221_, lean_object* v_bs_222_){
_start:
{
size_t v_sz_boxed_223_; size_t v_i_boxed_224_; lean_object* v_res_225_; 
v_sz_boxed_223_ = lean_unbox_usize(v_sz_220_);
lean_dec(v_sz_220_);
v_i_boxed_224_ = lean_unbox_usize(v_i_221_);
lean_dec(v_i_221_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_boxed_223_, v_i_boxed_224_, v_bs_222_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_ctor_set(v___x_231_, 3, v___x_229_);
lean_ctor_set(v___x_231_, 4, v___x_229_);
lean_ctor_set(v___x_231_, 5, v___x_229_);
lean_ctor_set(v___x_231_, 6, v___x_229_);
lean_ctor_set(v___x_231_, 7, v___x_229_);
lean_ctor_set(v___x_231_, 8, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(32u);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4(void){
_start:
{
size_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_235_ = ((size_t)5ULL);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_unsigned_to_nat(32u);
v___x_238_ = lean_mk_empty_array_with_capacity(v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3);
v___x_240_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_236_);
lean_ctor_set(v___x_240_, 3, v___x_236_);
lean_ctor_set_usize(v___x_240_, 4, v___x_235_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_box(1);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4);
v___x_243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v_options_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v_options_251_ = lean_ctor_get(v___y_246_, 2);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2);
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5);
lean_inc_ref(v_options_251_);
v___x_254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_254_, 0, v_env_250_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
lean_ctor_set(v___x_254_, 3, v_options_251_);
v___x_255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_msgData_245_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___boxed(lean_object* v_msgData_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msgData_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object* v_oldTraces_262_, lean_object* v_data_263_, lean_object* v_ref_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_fileName_269_; lean_object* v_fileMap_270_; lean_object* v_options_271_; lean_object* v_currRecDepth_272_; lean_object* v_maxRecDepth_273_; lean_object* v_ref_274_; lean_object* v_currNamespace_275_; lean_object* v_openDecls_276_; lean_object* v_initHeartbeats_277_; lean_object* v_maxHeartbeats_278_; lean_object* v_quotContext_279_; lean_object* v_currMacroScope_280_; uint8_t v_diag_281_; lean_object* v_cancelTk_x3f_282_; uint8_t v_suppressElabErrors_283_; lean_object* v_inheritedTraceOptions_284_; lean_object* v___x_285_; lean_object* v_traceState_286_; lean_object* v_traces_287_; lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v___x_290_; size_t v_sz_291_; size_t v___x_292_; lean_object* v___x_293_; lean_object* v_msg_294_; lean_object* v___x_295_; lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_333_; 
v_fileName_269_ = lean_ctor_get(v___y_266_, 0);
v_fileMap_270_ = lean_ctor_get(v___y_266_, 1);
v_options_271_ = lean_ctor_get(v___y_266_, 2);
v_currRecDepth_272_ = lean_ctor_get(v___y_266_, 3);
v_maxRecDepth_273_ = lean_ctor_get(v___y_266_, 4);
v_ref_274_ = lean_ctor_get(v___y_266_, 5);
v_currNamespace_275_ = lean_ctor_get(v___y_266_, 6);
v_openDecls_276_ = lean_ctor_get(v___y_266_, 7);
v_initHeartbeats_277_ = lean_ctor_get(v___y_266_, 8);
v_maxHeartbeats_278_ = lean_ctor_get(v___y_266_, 9);
v_quotContext_279_ = lean_ctor_get(v___y_266_, 10);
v_currMacroScope_280_ = lean_ctor_get(v___y_266_, 11);
v_diag_281_ = lean_ctor_get_uint8(v___y_266_, sizeof(void*)*14);
v_cancelTk_x3f_282_ = lean_ctor_get(v___y_266_, 12);
v_suppressElabErrors_283_ = lean_ctor_get_uint8(v___y_266_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_284_ = lean_ctor_get(v___y_266_, 13);
v___x_285_ = lean_st_ref_get(v___y_267_);
v_traceState_286_ = lean_ctor_get(v___x_285_, 4);
lean_inc_ref(v_traceState_286_);
lean_dec(v___x_285_);
v_traces_287_ = lean_ctor_get(v_traceState_286_, 0);
lean_inc_ref(v_traces_287_);
lean_dec_ref(v_traceState_286_);
v_ref_288_ = l_Lean_replaceRef(v_ref_264_, v_ref_274_);
lean_inc_ref(v_inheritedTraceOptions_284_);
lean_inc(v_cancelTk_x3f_282_);
lean_inc(v_currMacroScope_280_);
lean_inc(v_quotContext_279_);
lean_inc(v_maxHeartbeats_278_);
lean_inc(v_initHeartbeats_277_);
lean_inc(v_openDecls_276_);
lean_inc(v_currNamespace_275_);
lean_inc(v_maxRecDepth_273_);
lean_inc(v_currRecDepth_272_);
lean_inc_ref(v_options_271_);
lean_inc_ref(v_fileMap_270_);
lean_inc_ref(v_fileName_269_);
v___x_289_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_289_, 0, v_fileName_269_);
lean_ctor_set(v___x_289_, 1, v_fileMap_270_);
lean_ctor_set(v___x_289_, 2, v_options_271_);
lean_ctor_set(v___x_289_, 3, v_currRecDepth_272_);
lean_ctor_set(v___x_289_, 4, v_maxRecDepth_273_);
lean_ctor_set(v___x_289_, 5, v_ref_288_);
lean_ctor_set(v___x_289_, 6, v_currNamespace_275_);
lean_ctor_set(v___x_289_, 7, v_openDecls_276_);
lean_ctor_set(v___x_289_, 8, v_initHeartbeats_277_);
lean_ctor_set(v___x_289_, 9, v_maxHeartbeats_278_);
lean_ctor_set(v___x_289_, 10, v_quotContext_279_);
lean_ctor_set(v___x_289_, 11, v_currMacroScope_280_);
lean_ctor_set(v___x_289_, 12, v_cancelTk_x3f_282_);
lean_ctor_set(v___x_289_, 13, v_inheritedTraceOptions_284_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*14, v_diag_281_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*14 + 1, v_suppressElabErrors_283_);
v___x_290_ = l_Lean_PersistentArray_toArray___redArg(v_traces_287_);
lean_dec_ref(v_traces_287_);
v_sz_291_ = lean_array_size(v___x_290_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_291_, v___x_292_, v___x_290_);
v_msg_294_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_294_, 0, v_data_263_);
lean_ctor_set(v_msg_294_, 1, v_msg_265_);
lean_ctor_set(v_msg_294_, 2, v___x_293_);
v___x_295_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msg_294_, v___x_289_, v___y_267_);
lean_dec_ref(v___x_289_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_333_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_333_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_333_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v_traceState_301_; lean_object* v_env_302_; lean_object* v_nextMacroScope_303_; lean_object* v_ngen_304_; lean_object* v_auxDeclNGen_305_; lean_object* v_cache_306_; lean_object* v_messages_307_; lean_object* v_infoState_308_; lean_object* v_snapshotTasks_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_332_; 
v___x_300_ = lean_st_ref_take(v___y_267_);
v_traceState_301_ = lean_ctor_get(v___x_300_, 4);
v_env_302_ = lean_ctor_get(v___x_300_, 0);
v_nextMacroScope_303_ = lean_ctor_get(v___x_300_, 1);
v_ngen_304_ = lean_ctor_get(v___x_300_, 2);
v_auxDeclNGen_305_ = lean_ctor_get(v___x_300_, 3);
v_cache_306_ = lean_ctor_get(v___x_300_, 5);
v_messages_307_ = lean_ctor_get(v___x_300_, 6);
v_infoState_308_ = lean_ctor_get(v___x_300_, 7);
v_snapshotTasks_309_ = lean_ctor_get(v___x_300_, 8);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_332_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_snapshotTasks_309_);
lean_inc(v_infoState_308_);
lean_inc(v_messages_307_);
lean_inc(v_cache_306_);
lean_inc(v_traceState_301_);
lean_inc(v_auxDeclNGen_305_);
lean_inc(v_ngen_304_);
lean_inc(v_nextMacroScope_303_);
lean_inc(v_env_302_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint64_t v_tid_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
v_tid_313_ = lean_ctor_get_uint64(v_traceState_301_, sizeof(void*)*1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_traceState_301_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_traceState_301_, 0);
lean_dec(v_unused_331_);
v___x_315_ = v_traceState_301_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_traceState_301_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_ref_264_);
lean_ctor_set(v___x_317_, 1, v_a_296_);
v___x_318_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_262_, v___x_317_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_318_);
lean_ctor_set_uint64(v_reuseFailAlloc_329_, sizeof(void*)*1, v_tid_313_);
v___x_320_ = v_reuseFailAlloc_329_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v___x_320_);
v___x_322_ = v___x_311_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_env_302_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_nextMacroScope_303_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_ngen_304_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_auxDeclNGen_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_cache_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_messages_307_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_infoState_308_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_snapshotTasks_309_);
v___x_322_ = v_reuseFailAlloc_328_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_st_ref_set(v___y_267_, v___x_322_);
v___x_324_ = lean_box(0);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_324_);
v___x_326_ = v___x_298_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object* v_oldTraces_334_, lean_object* v_data_335_, lean_object* v_ref_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_334_, v_data_335_, v_ref_336_, v_msg_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object* v_e_342_){
_start:
{
if (lean_obj_tag(v_e_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = 2;
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 0;
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object* v_e_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_e_345_);
lean_dec_ref(v_e_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2(void){
_start:
{
lean_object* v___x_351_; double v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_float_of_nat(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5(void){
_start:
{
lean_object* v___x_356_; double v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(1000u);
v___x_357_ = lean_float_of_nat(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(lean_object* v_cls_358_, uint8_t v_collapsed_359_, lean_object* v_tag_360_, lean_object* v_opts_361_, uint8_t v_clsEnabled_362_, lean_object* v_oldTraces_363_, lean_object* v_msg_364_, lean_object* v_resStartStop_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_460_; 
v_fst_369_ = lean_ctor_get(v_resStartStop_365_, 0);
v_snd_370_ = lean_ctor_get(v_resStartStop_365_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_resStartStop_365_);
if (v_isSharedCheck_460_ == 0)
{
v___x_372_ = v_resStartStop_365_;
v_isShared_373_ = v_isSharedCheck_460_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_inc(v_fst_369_);
lean_dec(v_resStartStop_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_460_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v_data_377_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_459_; 
v_fst_380_ = lean_ctor_get(v_snd_370_, 0);
v_snd_381_ = lean_ctor_get(v_snd_370_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_snd_370_);
if (v_isSharedCheck_459_ == 0)
{
v___x_383_ = v_snd_370_;
v_isShared_384_ = v_isSharedCheck_459_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_inc(v_fst_380_);
lean_dec(v_snd_370_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_459_;
goto v_resetjp_382_;
}
v___jp_374_:
{
lean_object* v___x_378_; 
lean_inc(v___y_376_);
v___x_378_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_363_, v_data_377_, v___y_376_, v___y_375_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_378_);
v___x_379_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_369_);
return v___x_379_;
}
else
{
lean_dec(v_fst_369_);
return v___x_378_;
}
}
v_resetjp_382_:
{
lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___y_388_; lean_object* v_a_389_; uint8_t v___y_413_; double v___y_444_; 
v___x_385_ = l_Lean_trace_profiler;
v___x_386_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_361_, v___x_385_);
if (v___x_386_ == 0)
{
v___y_413_ = v___x_386_;
goto v___jp_412_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = l_Lean_trace_profiler_useHeartbeats;
v___x_450_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_361_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; double v___x_453_; double v___x_454_; double v___x_455_; 
v___x_451_ = l_Lean_trace_profiler_threshold;
v___x_452_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_361_, v___x_451_);
v___x_453_ = lean_float_of_nat(v___x_452_);
v___x_454_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5);
v___x_455_ = lean_float_div(v___x_453_, v___x_454_);
v___y_444_ = v___x_455_;
goto v___jp_443_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; double v___x_458_; 
v___x_456_ = l_Lean_trace_profiler_threshold;
v___x_457_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_361_, v___x_456_);
v___x_458_ = lean_float_of_nat(v___x_457_);
v___y_444_ = v___x_458_;
goto v___jp_443_;
}
}
v___jp_387_:
{
uint8_t v_result_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v_result_390_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_fst_369_);
v___x_391_ = l_Lean_TraceResult_toEmoji(v_result_390_);
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
v___x_393_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 7);
lean_ctor_set(v___x_383_, 1, v___x_393_);
lean_ctor_set(v___x_383_, 0, v___x_392_);
v___x_395_ = v___x_383_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_406_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v_m_397_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 7);
lean_ctor_set(v___x_372_, 1, v_a_389_);
lean_ctor_set(v___x_372_, 0, v___x_395_);
v_m_397_ = v___x_372_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_a_389_);
v_m_397_ = v_reuseFailAlloc_405_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; double v___x_400_; lean_object* v_data_401_; 
v___x_398_ = lean_box(v_result_390_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2);
lean_inc_ref(v_tag_360_);
lean_inc_ref(v___x_399_);
lean_inc(v_cls_358_);
v_data_401_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_401_, 0, v_cls_358_);
lean_ctor_set(v_data_401_, 1, v___x_399_);
lean_ctor_set(v_data_401_, 2, v_tag_360_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3, v___x_400_);
lean_ctor_set_float(v_data_401_, sizeof(void*)*3 + 8, v___x_400_);
lean_ctor_set_uint8(v_data_401_, sizeof(void*)*3 + 16, v_collapsed_359_);
if (v___x_386_ == 0)
{
lean_dec_ref(v___x_399_);
lean_dec(v_snd_381_);
lean_dec(v_fst_380_);
lean_dec_ref(v_tag_360_);
lean_dec(v_cls_358_);
v___y_375_ = v_m_397_;
v___y_376_ = v___y_388_;
v_data_377_ = v_data_401_;
goto v___jp_374_;
}
else
{
lean_object* v_data_402_; double v___x_403_; double v___x_404_; 
lean_dec_ref(v_data_401_);
v_data_402_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_402_, 0, v_cls_358_);
lean_ctor_set(v_data_402_, 1, v___x_399_);
lean_ctor_set(v_data_402_, 2, v_tag_360_);
v___x_403_ = lean_unbox_float(v_fst_380_);
lean_dec(v_fst_380_);
lean_ctor_set_float(v_data_402_, sizeof(void*)*3, v___x_403_);
v___x_404_ = lean_unbox_float(v_snd_381_);
lean_dec(v_snd_381_);
lean_ctor_set_float(v_data_402_, sizeof(void*)*3 + 8, v___x_404_);
lean_ctor_set_uint8(v_data_402_, sizeof(void*)*3 + 16, v_collapsed_359_);
v___y_375_ = v_m_397_;
v___y_376_ = v___y_388_;
v_data_377_ = v_data_402_;
goto v___jp_374_;
}
}
}
}
v___jp_407_:
{
lean_object* v_ref_408_; lean_object* v___x_409_; 
v_ref_408_ = lean_ctor_get(v___y_366_, 5);
lean_inc(v___y_367_);
lean_inc_ref(v___y_366_);
lean_inc(v_fst_369_);
v___x_409_ = lean_apply_4(v_msg_364_, v_fst_369_, v___y_366_, v___y_367_, lean_box(0));
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v___x_409_);
v___y_388_ = v_ref_408_;
v_a_389_ = v_a_410_;
goto v___jp_387_;
}
else
{
lean_object* v___x_411_; 
lean_dec_ref(v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4);
v___y_388_ = v_ref_408_;
v_a_389_ = v___x_411_;
goto v___jp_387_;
}
}
v___jp_412_:
{
if (v_clsEnabled_362_ == 0)
{
if (v___y_413_ == 0)
{
lean_object* v___x_414_; lean_object* v_traceState_415_; lean_object* v_env_416_; lean_object* v_nextMacroScope_417_; lean_object* v_ngen_418_; lean_object* v_auxDeclNGen_419_; lean_object* v_cache_420_; lean_object* v_messages_421_; lean_object* v_infoState_422_; lean_object* v_snapshotTasks_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_442_; 
lean_del_object(v___x_383_);
lean_dec(v_snd_381_);
lean_dec(v_fst_380_);
lean_del_object(v___x_372_);
lean_dec_ref(v_msg_364_);
lean_dec_ref(v_tag_360_);
lean_dec(v_cls_358_);
v___x_414_ = lean_st_ref_take(v___y_367_);
v_traceState_415_ = lean_ctor_get(v___x_414_, 4);
v_env_416_ = lean_ctor_get(v___x_414_, 0);
v_nextMacroScope_417_ = lean_ctor_get(v___x_414_, 1);
v_ngen_418_ = lean_ctor_get(v___x_414_, 2);
v_auxDeclNGen_419_ = lean_ctor_get(v___x_414_, 3);
v_cache_420_ = lean_ctor_get(v___x_414_, 5);
v_messages_421_ = lean_ctor_get(v___x_414_, 6);
v_infoState_422_ = lean_ctor_get(v___x_414_, 7);
v_snapshotTasks_423_ = lean_ctor_get(v___x_414_, 8);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_442_ == 0)
{
v___x_425_ = v___x_414_;
v_isShared_426_ = v_isSharedCheck_442_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snapshotTasks_423_);
lean_inc(v_infoState_422_);
lean_inc(v_messages_421_);
lean_inc(v_cache_420_);
lean_inc(v_traceState_415_);
lean_inc(v_auxDeclNGen_419_);
lean_inc(v_ngen_418_);
lean_inc(v_nextMacroScope_417_);
lean_inc(v_env_416_);
lean_dec(v___x_414_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_442_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
uint64_t v_tid_427_; lean_object* v_traces_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_441_; 
v_tid_427_ = lean_ctor_get_uint64(v_traceState_415_, sizeof(void*)*1);
v_traces_428_ = lean_ctor_get(v_traceState_415_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_traceState_415_);
if (v_isSharedCheck_441_ == 0)
{
v___x_430_ = v_traceState_415_;
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_traces_428_);
lean_dec(v_traceState_415_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_363_, v_traces_428_);
lean_dec_ref(v_traces_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_432_);
lean_ctor_set_uint64(v_reuseFailAlloc_440_, sizeof(void*)*1, v_tid_427_);
v___x_434_ = v_reuseFailAlloc_440_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 4, v___x_434_);
v___x_436_ = v___x_425_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_env_416_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_nextMacroScope_417_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_ngen_418_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_auxDeclNGen_419_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 5, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_439_, 6, v_messages_421_);
lean_ctor_set(v_reuseFailAlloc_439_, 7, v_infoState_422_);
lean_ctor_set(v_reuseFailAlloc_439_, 8, v_snapshotTasks_423_);
v___x_436_ = v_reuseFailAlloc_439_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_st_ref_set(v___y_367_, v___x_436_);
v___x_438_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_369_);
return v___x_438_;
}
}
}
}
}
else
{
goto v___jp_407_;
}
}
else
{
goto v___jp_407_;
}
}
v___jp_443_:
{
double v___x_445_; double v___x_446_; double v___x_447_; uint8_t v___x_448_; 
v___x_445_ = lean_unbox_float(v_snd_381_);
v___x_446_ = lean_unbox_float(v_fst_380_);
v___x_447_ = lean_float_sub(v___x_445_, v___x_446_);
v___x_448_ = lean_float_decLt(v___y_444_, v___x_447_);
v___y_413_ = v___x_448_;
goto v___jp_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_cls_461_, lean_object* v_collapsed_462_, lean_object* v_tag_463_, lean_object* v_opts_464_, lean_object* v_clsEnabled_465_, lean_object* v_oldTraces_466_, lean_object* v_msg_467_, lean_object* v_resStartStop_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v_collapsed_boxed_472_; uint8_t v_clsEnabled_boxed_473_; lean_object* v_res_474_; 
v_collapsed_boxed_472_ = lean_unbox(v_collapsed_462_);
v_clsEnabled_boxed_473_ = lean_unbox(v_clsEnabled_465_);
v_res_474_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v_cls_461_, v_collapsed_boxed_472_, v_tag_463_, v_opts_464_, v_clsEnabled_boxed_473_, v_oldTraces_466_, v_msg_467_, v_resStartStop_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v_opts_464_);
return v_res_474_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_475_; double v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1000000000u);
v___x_476_ = lean_float_of_nat(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__3(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_482_, uint8_t v___x_483_, lean_object* v___x_484_, lean_object* v___f_485_, lean_object* v_declNames_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_fileName_491_; lean_object* v_fileMap_492_; lean_object* v_options_493_; lean_object* v_currRecDepth_494_; lean_object* v_ref_495_; lean_object* v_currNamespace_496_; lean_object* v_openDecls_497_; lean_object* v_initHeartbeats_498_; lean_object* v_maxHeartbeats_499_; lean_object* v_quotContext_500_; lean_object* v_currMacroScope_501_; lean_object* v_cancelTk_x3f_502_; uint8_t v_suppressElabErrors_503_; lean_object* v_inheritedTraceOptions_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_642_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_fileName_491_ = lean_ctor_get(v___y_487_, 0);
v_fileMap_492_ = lean_ctor_get(v___y_487_, 1);
v_options_493_ = lean_ctor_get(v___y_487_, 2);
v_currRecDepth_494_ = lean_ctor_get(v___y_487_, 3);
v_ref_495_ = lean_ctor_get(v___y_487_, 5);
v_currNamespace_496_ = lean_ctor_get(v___y_487_, 6);
v_openDecls_497_ = lean_ctor_get(v___y_487_, 7);
v_initHeartbeats_498_ = lean_ctor_get(v___y_487_, 8);
v_maxHeartbeats_499_ = lean_ctor_get(v___y_487_, 9);
v_quotContext_500_ = lean_ctor_get(v___y_487_, 10);
v_currMacroScope_501_ = lean_ctor_get(v___y_487_, 11);
v_cancelTk_x3f_502_ = lean_ctor_get(v___y_487_, 12);
v_suppressElabErrors_503_ = lean_ctor_get_uint8(v___y_487_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_504_ = lean_ctor_get(v___y_487_, 13);
v_isSharedCheck_642_ = !lean_is_exclusive(v___y_487_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___y_487_, 4);
lean_dec(v_unused_643_);
v___x_506_ = v___y_487_;
v_isShared_507_ = v_isSharedCheck_642_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_inheritedTraceOptions_504_);
lean_inc(v_cancelTk_x3f_502_);
lean_inc(v_currMacroScope_501_);
lean_inc(v_quotContext_500_);
lean_inc(v_maxHeartbeats_499_);
lean_inc(v_initHeartbeats_498_);
lean_inc(v_openDecls_497_);
lean_inc(v_currNamespace_496_);
lean_inc(v_ref_495_);
lean_inc(v_currRecDepth_494_);
lean_inc(v_options_493_);
lean_inc(v_fileMap_492_);
lean_inc(v_fileName_491_);
lean_dec(v___y_487_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_642_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_env_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v_a_518_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v_a_536_; uint8_t v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v_fileName_592_; lean_object* v_fileMap_593_; lean_object* v_currRecDepth_594_; lean_object* v_ref_595_; lean_object* v_currNamespace_596_; lean_object* v_openDecls_597_; lean_object* v_initHeartbeats_598_; lean_object* v_maxHeartbeats_599_; lean_object* v_quotContext_600_; lean_object* v_currMacroScope_601_; lean_object* v_cancelTk_x3f_602_; uint8_t v_suppressElabErrors_603_; lean_object* v_inheritedTraceOptions_604_; lean_object* v___y_605_; uint8_t v___y_620_; uint8_t v___x_641_; 
v_env_508_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_490_);
v___x_509_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_510_ = 0;
v___x_511_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_options_493_, v___x_509_, v___x_510_);
v___x_589_ = l_Lean_diagnostics;
v___x_590_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_511_, v___x_589_);
v___x_641_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_508_);
lean_dec_ref(v_env_508_);
if (v___x_641_ == 0)
{
if (v___x_590_ == 0)
{
v_fileName_592_ = v_fileName_491_;
v_fileMap_593_ = v_fileMap_492_;
v_currRecDepth_594_ = v_currRecDepth_494_;
v_ref_595_ = v_ref_495_;
v_currNamespace_596_ = v_currNamespace_496_;
v_openDecls_597_ = v_openDecls_497_;
v_initHeartbeats_598_ = v_initHeartbeats_498_;
v_maxHeartbeats_599_ = v_maxHeartbeats_499_;
v_quotContext_600_ = v_quotContext_500_;
v_currMacroScope_601_ = v_currMacroScope_501_;
v_cancelTk_x3f_602_ = v_cancelTk_x3f_502_;
v_suppressElabErrors_603_ = v_suppressElabErrors_503_;
v_inheritedTraceOptions_604_ = v_inheritedTraceOptions_504_;
v___y_605_ = v___y_488_;
goto v___jp_591_;
}
else
{
v___y_620_ = v___x_641_;
goto v___jp_619_;
}
}
else
{
v___y_620_ = v___x_590_;
goto v___jp_619_;
}
v___jp_512_:
{
lean_object* v___x_519_; double v___x_520_; double v___x_521_; double v___x_522_; double v___x_523_; double v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_519_ = lean_io_mono_nanos_now();
v___x_520_ = lean_float_of_nat(v___y_517_);
v___x_521_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_522_ = lean_float_div(v___x_520_, v___x_521_);
v___x_523_ = lean_float_of_nat(v___x_519_);
v___x_524_ = lean_float_div(v___x_523_, v___x_521_);
v___x_525_ = lean_box_float(v___x_522_);
v___x_526_ = lean_box_float(v___x_524_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_a_518_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_482_, v___x_483_, v___x_484_, v___x_511_, v___y_514_, v___y_516_, v___f_485_, v___x_528_, v___y_513_, v___y_515_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___x_511_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_537_; double v___x_538_; double v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_537_ = lean_io_get_num_heartbeats();
v___x_538_ = lean_float_of_nat(v___y_533_);
v___x_539_ = lean_float_of_nat(v___x_537_);
v___x_540_ = lean_box_float(v___x_538_);
v___x_541_ = lean_box_float(v___x_539_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_a_536_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_482_, v___x_483_, v___x_484_, v___x_511_, v___y_532_, v___y_535_, v___f_485_, v___x_543_, v___y_531_, v___y_534_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___x_511_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_548_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_552_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_511_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_io_mono_nanos_now();
v___x_554_ = l_Lean_Compiler_LCNF_main(v_declNames_486_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 1);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_513_ = v___y_547_;
v___y_514_ = v___y_546_;
v___y_515_ = v___y_548_;
v___y_516_ = v_a_550_;
v___y_517_ = v___x_553_;
v_a_518_ = v___x_560_;
goto v___jp_512_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 0);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v___y_513_ = v___y_547_;
v___y_514_ = v___y_546_;
v___y_515_ = v___y_548_;
v___y_516_ = v_a_550_;
v___y_517_ = v___x_553_;
v_a_518_ = v___x_568_;
goto v___jp_512_;
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_io_get_num_heartbeats();
v___x_572_ = l_Lean_Compiler_LCNF_main(v_declNames_486_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 1);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v___y_531_ = v___y_547_;
v___y_532_ = v___y_546_;
v___y_533_ = v___x_571_;
v___y_534_ = v___y_548_;
v___y_535_ = v_a_550_;
v_a_536_ = v___x_578_;
goto v___jp_530_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_531_ = v___y_547_;
v___y_532_ = v___y_546_;
v___y_533_ = v___x_571_;
v___y_534_ = v___y_548_;
v___y_535_ = v_a_550_;
v_a_536_ = v___x_586_;
goto v___jp_530_;
}
}
}
}
}
v___jp_591_:
{
uint8_t v_hasTrace_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v_hasTrace_606_ = lean_ctor_get_uint8(v___x_511_, sizeof(void*)*1);
v___x_607_ = l_Lean_maxRecDepth;
v___x_608_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___x_511_, v___x_607_);
lean_inc_ref(v_inheritedTraceOptions_604_);
lean_inc_ref(v___x_511_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 13, v_inheritedTraceOptions_604_);
lean_ctor_set(v___x_506_, 12, v_cancelTk_x3f_602_);
lean_ctor_set(v___x_506_, 11, v_currMacroScope_601_);
lean_ctor_set(v___x_506_, 10, v_quotContext_600_);
lean_ctor_set(v___x_506_, 9, v_maxHeartbeats_599_);
lean_ctor_set(v___x_506_, 8, v_initHeartbeats_598_);
lean_ctor_set(v___x_506_, 7, v_openDecls_597_);
lean_ctor_set(v___x_506_, 6, v_currNamespace_596_);
lean_ctor_set(v___x_506_, 5, v_ref_595_);
lean_ctor_set(v___x_506_, 4, v___x_608_);
lean_ctor_set(v___x_506_, 3, v_currRecDepth_594_);
lean_ctor_set(v___x_506_, 2, v___x_511_);
lean_ctor_set(v___x_506_, 1, v_fileMap_593_);
lean_ctor_set(v___x_506_, 0, v_fileName_592_);
v___x_610_ = v___x_506_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_fileName_592_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_fileMap_593_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_currRecDepth_594_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v_ref_595_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_currNamespace_596_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_openDecls_597_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_initHeartbeats_598_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_maxHeartbeats_599_);
lean_ctor_set(v_reuseFailAlloc_618_, 10, v_quotContext_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 11, v_currMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 12, v_cancelTk_x3f_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 13, v_inheritedTraceOptions_604_);
v___x_610_ = v_reuseFailAlloc_618_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*14, v___x_590_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*14 + 1, v_suppressElabErrors_603_);
if (v_hasTrace_606_ == 0)
{
lean_object* v___x_611_; 
lean_dec_ref(v_inheritedTraceOptions_604_);
lean_dec_ref(v___x_511_);
lean_dec_ref(v___f_485_);
lean_dec_ref(v___x_484_);
lean_dec(v___x_482_);
v___x_611_ = l_Lean_Compiler_LCNF_main(v_declNames_486_, v___x_610_, v___y_605_);
lean_dec_ref(v___x_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
lean_inc(v___x_482_);
v___x_613_ = l_Lean_Name_append(v___x_612_, v___x_482_);
v___x_614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_604_, v___x_511_, v___x_613_);
lean_dec(v___x_613_);
lean_dec_ref(v_inheritedTraceOptions_604_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = l_Lean_trace_profiler;
v___x_616_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_511_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v___x_511_);
lean_dec_ref(v___f_485_);
lean_dec_ref(v___x_484_);
lean_dec(v___x_482_);
v___x_617_ = l_Lean_Compiler_LCNF_main(v_declNames_486_, v___x_610_, v___y_605_);
lean_dec_ref(v___x_610_);
return v___x_617_;
}
else
{
v___y_546_ = v___x_614_;
v___y_547_ = v___x_610_;
v___y_548_ = v___y_605_;
goto v___jp_545_;
}
}
else
{
v___y_546_ = v___x_614_;
v___y_547_ = v___x_610_;
v___y_548_ = v___y_605_;
goto v___jp_545_;
}
}
}
}
v___jp_619_:
{
if (v___y_620_ == 0)
{
lean_object* v___x_621_; lean_object* v_env_622_; lean_object* v_nextMacroScope_623_; lean_object* v_ngen_624_; lean_object* v_auxDeclNGen_625_; lean_object* v_traceState_626_; lean_object* v_messages_627_; lean_object* v_infoState_628_; lean_object* v_snapshotTasks_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_639_; 
v___x_621_ = lean_st_ref_take(v___y_488_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
v_nextMacroScope_623_ = lean_ctor_get(v___x_621_, 1);
v_ngen_624_ = lean_ctor_get(v___x_621_, 2);
v_auxDeclNGen_625_ = lean_ctor_get(v___x_621_, 3);
v_traceState_626_ = lean_ctor_get(v___x_621_, 4);
v_messages_627_ = lean_ctor_get(v___x_621_, 6);
v_infoState_628_ = lean_ctor_get(v___x_621_, 7);
v_snapshotTasks_629_ = lean_ctor_get(v___x_621_, 8);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_621_, 5);
lean_dec(v_unused_640_);
v___x_631_ = v___x_621_;
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snapshotTasks_629_);
lean_inc(v_infoState_628_);
lean_inc(v_messages_627_);
lean_inc(v_traceState_626_);
lean_inc(v_auxDeclNGen_625_);
lean_inc(v_ngen_624_);
lean_inc(v_nextMacroScope_623_);
lean_inc(v_env_622_);
lean_dec(v___x_621_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = l_Lean_Kernel_enableDiag(v_env_622_, v___x_590_);
v___x_634_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__3, &l_Lean_Compiler_compile___lam__1___closed__3_once, _init_l_Lean_Compiler_compile___lam__1___closed__3);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 5, v___x_634_);
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_nextMacroScope_623_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_ngen_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_auxDeclNGen_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_traceState_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_messages_627_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_infoState_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v_snapshotTasks_629_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = lean_st_ref_set(v___y_488_, v___x_636_);
v_fileName_592_ = v_fileName_491_;
v_fileMap_593_ = v_fileMap_492_;
v_currRecDepth_594_ = v_currRecDepth_494_;
v_ref_595_ = v_ref_495_;
v_currNamespace_596_ = v_currNamespace_496_;
v_openDecls_597_ = v_openDecls_497_;
v_initHeartbeats_598_ = v_initHeartbeats_498_;
v_maxHeartbeats_599_ = v_maxHeartbeats_499_;
v_quotContext_600_ = v_quotContext_500_;
v_currMacroScope_601_ = v_currMacroScope_501_;
v_cancelTk_x3f_602_ = v_cancelTk_x3f_502_;
v_suppressElabErrors_603_ = v_suppressElabErrors_503_;
v_inheritedTraceOptions_604_ = v_inheritedTraceOptions_504_;
v___y_605_ = v___y_488_;
goto v___jp_591_;
}
}
}
else
{
v_fileName_592_ = v_fileName_491_;
v_fileMap_593_ = v_fileMap_492_;
v_currRecDepth_594_ = v_currRecDepth_494_;
v_ref_595_ = v_ref_495_;
v_currNamespace_596_ = v_currNamespace_496_;
v_openDecls_597_ = v_openDecls_497_;
v_initHeartbeats_598_ = v_initHeartbeats_498_;
v_maxHeartbeats_599_ = v_maxHeartbeats_499_;
v_quotContext_600_ = v_quotContext_500_;
v_currMacroScope_601_ = v_currMacroScope_501_;
v_cancelTk_x3f_602_ = v_cancelTk_x3f_502_;
v_suppressElabErrors_603_ = v_suppressElabErrors_503_;
v_inheritedTraceOptions_604_ = v_inheritedTraceOptions_504_;
v___y_605_ = v___y_488_;
goto v___jp_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___f_647_, lean_object* v_declNames_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___x_7041__boxed_652_; lean_object* v_res_653_; 
v___x_7041__boxed_652_ = lean_unbox(v___x_645_);
v_res_653_ = l_Lean_Compiler_compile___lam__1(v___x_644_, v___x_7041__boxed_652_, v___x_646_, v___f_647_, v_declNames_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_options_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_options_663_ = lean_ctor_get(v_a_660_, 2);
lean_inc_ref(v_declNames_659_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_664_, 0, v_declNames_659_);
v___x_665_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_666_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_667_ = 1;
v___x_668_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_669_ = lean_box(v___x_667_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 8, 5);
lean_closure_set(v___f_670_, 0, v___x_666_);
lean_closure_set(v___f_670_, 1, v___x_669_);
lean_closure_set(v___f_670_, 2, v___x_668_);
lean_closure_set(v___f_670_, 3, v___f_664_);
lean_closure_set(v___f_670_, 4, v_declNames_659_);
v___x_671_ = lean_box(0);
v___x_672_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_665_, v_options_663_, v___f_670_, v___x_671_, v_a_660_, v_a_661_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Compiler_compile(v_declNames_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_00_u03b1_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_679_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_00_u03b1_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_00_u03b1_684_, v_x_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_751_ = 0;
v___x_752_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_753_ = l_Lean_registerTraceClass(v___x_750_, v___x_751_, v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v___x_753_);
v___x_754_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_755_ = l_Lean_registerTraceClass(v___x_754_, v___x_751_, v___x_752_);
return v___x_755_;
}
else
{
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_757_;
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

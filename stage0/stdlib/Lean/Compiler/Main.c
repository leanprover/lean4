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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
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
lean_dec_ref_known(v___x_20_, 1);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref_known(v_val_21_, 1);
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
v___x_62_ = lean_st_ref_put(v___y_35_, v___x_61_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(size_t v_sz_187_, size_t v_i_188_, lean_object* v_bs_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_lt(v_i_188_, v_sz_187_);
if (v___x_190_ == 0)
{
return v_bs_189_;
}
else
{
lean_object* v_v_191_; lean_object* v_msg_192_; lean_object* v___x_193_; lean_object* v_bs_x27_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v_v_191_ = lean_array_uget_borrowed(v_bs_189_, v_i_188_);
v_msg_192_ = lean_ctor_get(v_v_191_, 1);
lean_inc_ref(v_msg_192_);
v___x_193_ = lean_unsigned_to_nat(0u);
v_bs_x27_194_ = lean_array_uset(v_bs_189_, v_i_188_, v___x_193_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_add(v_i_188_, v___x_195_);
v___x_197_ = lean_array_uset(v_bs_x27_194_, v_i_188_, v_msg_192_);
v_i_188_ = v___x_196_;
v_bs_189_ = v___x_197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8___boxed(lean_object* v_sz_199_, lean_object* v_i_200_, lean_object* v_bs_201_){
_start:
{
size_t v_sz_boxed_202_; size_t v_i_boxed_203_; lean_object* v_res_204_; 
v_sz_boxed_202_ = lean_unbox_usize(v_sz_199_);
lean_dec(v_sz_199_);
v_i_boxed_203_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(v_sz_boxed_202_, v_i_boxed_203_, v_bs_201_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
lean_ctor_set(v___x_210_, 3, v___x_209_);
lean_ctor_set(v___x_210_, 4, v___x_208_);
lean_ctor_set(v___x_210_, 5, v___x_208_);
lean_ctor_set(v___x_210_, 6, v___x_208_);
lean_ctor_set(v___x_210_, 7, v___x_208_);
lean_ctor_set(v___x_210_, 8, v___x_208_);
lean_ctor_set(v___x_210_, 9, v___x_208_);
lean_ctor_set(v___x_210_, 10, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_unsigned_to_nat(32u);
v___x_212_ = lean_mk_empty_array_with_capacity(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4(void){
_start:
{
size_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_214_ = ((size_t)5ULL);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_unsigned_to_nat(32u);
v___x_217_ = lean_mk_empty_array_with_capacity(v___x_216_);
v___x_218_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3);
v___x_219_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_215_);
lean_ctor_set(v___x_219_, 3, v___x_215_);
lean_ctor_set_usize(v___x_219_, 4, v___x_214_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_box(1);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4);
v___x_222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(lean_object* v_msgData_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_toCold_229_; lean_object* v_env_230_; lean_object* v_options_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_toCold_229_ = lean_ctor_get(v___y_225_, 0);
v_env_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_230_);
lean_dec(v___x_228_);
v_options_231_ = lean_ctor_get(v_toCold_229_, 2);
v___x_232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2);
v___x_233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5);
lean_inc_ref(v_options_231_);
v___x_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_234_, 0, v_env_230_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_ctor_set(v___x_234_, 3, v_options_231_);
v___x_235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_msgData_224_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(v_msgData_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object* v_oldTraces_242_, lean_object* v_data_243_, lean_object* v_ref_244_, lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_toCold_249_; lean_object* v_currRecDepth_250_; lean_object* v_ref_251_; uint8_t v_diag_252_; uint8_t v_suppressElabErrors_253_; lean_object* v___x_254_; lean_object* v_traceState_255_; lean_object* v_traces_256_; lean_object* v_ref_257_; lean_object* v___x_258_; lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v___x_262_; lean_object* v_msg_263_; lean_object* v___x_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_302_; 
v_toCold_249_ = lean_ctor_get(v___y_246_, 0);
v_currRecDepth_250_ = lean_ctor_get(v___y_246_, 1);
v_ref_251_ = lean_ctor_get(v___y_246_, 2);
v_diag_252_ = lean_ctor_get_uint8(v___y_246_, sizeof(void*)*3);
v_suppressElabErrors_253_ = lean_ctor_get_uint8(v___y_246_, sizeof(void*)*3 + 1);
v___x_254_ = lean_st_ref_get(v___y_247_);
v_traceState_255_ = lean_ctor_get(v___x_254_, 4);
lean_inc_ref(v_traceState_255_);
lean_dec(v___x_254_);
v_traces_256_ = lean_ctor_get(v_traceState_255_, 0);
lean_inc_ref(v_traces_256_);
lean_dec_ref(v_traceState_255_);
v_ref_257_ = l_Lean_replaceRef(v_ref_244_, v_ref_251_);
lean_inc(v_currRecDepth_250_);
lean_inc_ref(v_toCold_249_);
v___x_258_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_258_, 0, v_toCold_249_);
lean_ctor_set(v___x_258_, 1, v_currRecDepth_250_);
lean_ctor_set(v___x_258_, 2, v_ref_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3, v_diag_252_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3 + 1, v_suppressElabErrors_253_);
v___x_259_ = l_Lean_PersistentArray_toArray___redArg(v_traces_256_);
lean_dec_ref(v_traces_256_);
v_sz_260_ = lean_array_size(v___x_259_);
v___x_261_ = ((size_t)0ULL);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(v_sz_260_, v___x_261_, v___x_259_);
v_msg_263_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_263_, 0, v_data_243_);
lean_ctor_set(v_msg_263_, 1, v_msg_245_);
lean_ctor_set(v_msg_263_, 2, v___x_262_);
v___x_264_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(v_msg_263_, v___x_258_, v___y_247_);
lean_dec_ref_known(v___x_258_, 3);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_302_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_302_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_302_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v_traceState_270_; lean_object* v_env_271_; lean_object* v_nextMacroScope_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_cache_275_; lean_object* v_messages_276_; lean_object* v_infoState_277_; lean_object* v_snapshotTasks_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_301_; 
v___x_269_ = lean_st_ref_take(v___y_247_);
v_traceState_270_ = lean_ctor_get(v___x_269_, 4);
v_env_271_ = lean_ctor_get(v___x_269_, 0);
v_nextMacroScope_272_ = lean_ctor_get(v___x_269_, 1);
v_ngen_273_ = lean_ctor_get(v___x_269_, 2);
v_auxDeclNGen_274_ = lean_ctor_get(v___x_269_, 3);
v_cache_275_ = lean_ctor_get(v___x_269_, 5);
v_messages_276_ = lean_ctor_get(v___x_269_, 6);
v_infoState_277_ = lean_ctor_get(v___x_269_, 7);
v_snapshotTasks_278_ = lean_ctor_get(v___x_269_, 8);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_301_ == 0)
{
v___x_280_ = v___x_269_;
v_isShared_281_ = v_isSharedCheck_301_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snapshotTasks_278_);
lean_inc(v_infoState_277_);
lean_inc(v_messages_276_);
lean_inc(v_cache_275_);
lean_inc(v_traceState_270_);
lean_inc(v_auxDeclNGen_274_);
lean_inc(v_ngen_273_);
lean_inc(v_nextMacroScope_272_);
lean_inc(v_env_271_);
lean_dec(v___x_269_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_301_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint64_t v_tid_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_299_; 
v_tid_282_ = lean_ctor_get_uint64(v_traceState_270_, sizeof(void*)*1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_traceState_270_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_traceState_270_, 0);
lean_dec(v_unused_300_);
v___x_284_ = v_traceState_270_;
v_isShared_285_ = v_isSharedCheck_299_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_traceState_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_299_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_ref_244_);
lean_ctor_set(v___x_286_, 1, v_a_265_);
v___x_287_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_242_, v___x_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_287_);
lean_ctor_set_uint64(v_reuseFailAlloc_298_, sizeof(void*)*1, v_tid_282_);
v___x_289_ = v_reuseFailAlloc_298_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_291_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 4, v___x_289_);
v___x_291_ = v___x_280_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_env_271_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_nextMacroScope_272_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_297_, 5, v_cache_275_);
lean_ctor_set(v_reuseFailAlloc_297_, 6, v_messages_276_);
lean_ctor_set(v_reuseFailAlloc_297_, 7, v_infoState_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 8, v_snapshotTasks_278_);
v___x_291_ = v_reuseFailAlloc_297_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = lean_st_ref_put(v___y_247_, v___x_291_);
v___x_293_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_293_);
v___x_295_ = v___x_267_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object* v_oldTraces_303_, lean_object* v_data_304_, lean_object* v_ref_305_, lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_oldTraces_303_, v_data_304_, v_ref_305_, v_msg_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_e_311_){
_start:
{
if (lean_obj_tag(v_e_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 2;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_e_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_e_314_);
lean_dec_ref(v_e_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_319_ = lean_ctor_get(v_x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v_x_317_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v_x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 1);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v_x_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v_x_317_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_x_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 0);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg___boxed(lean_object* v_x_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_x_335_);
return v_res_337_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0(void){
_start:
{
lean_object* v___x_338_; double v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_float_of_nat(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3(void){
_start:
{
lean_object* v___x_343_; double v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1000u);
v___x_344_ = lean_float_of_nat(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(lean_object* v_cls_345_, uint8_t v_collapsed_346_, lean_object* v_tag_347_, lean_object* v_opts_348_, uint8_t v_clsEnabled_349_, lean_object* v_oldTraces_350_, lean_object* v_msg_351_, lean_object* v_resStartStop_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v_data_361_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___y_369_; lean_object* v_a_370_; uint8_t v___y_385_; double v___y_416_; 
v_fst_356_ = lean_ctor_get(v_resStartStop_352_, 0);
lean_inc(v_fst_356_);
v_snd_357_ = lean_ctor_get(v_resStartStop_352_, 1);
lean_inc(v_snd_357_);
lean_dec_ref(v_resStartStop_352_);
v_fst_364_ = lean_ctor_get(v_snd_357_, 0);
lean_inc(v_fst_364_);
v_snd_365_ = lean_ctor_get(v_snd_357_, 1);
lean_inc(v_snd_365_);
lean_dec(v_snd_357_);
v___x_366_ = l_Lean_trace_profiler;
v___x_367_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_348_, v___x_366_);
if (v___x_367_ == 0)
{
v___y_385_ = v___x_367_;
goto v___jp_384_;
}
else
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = l_Lean_trace_profiler_useHeartbeats;
v___x_422_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_348_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; double v___x_425_; double v___x_426_; double v___x_427_; 
v___x_423_ = l_Lean_trace_profiler_threshold;
v___x_424_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_348_, v___x_423_);
v___x_425_ = lean_float_of_nat(v___x_424_);
v___x_426_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3);
v___x_427_ = lean_float_div(v___x_425_, v___x_426_);
v___y_416_ = v___x_427_;
goto v___jp_415_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; double v___x_430_; 
v___x_428_ = l_Lean_trace_profiler_threshold;
v___x_429_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_348_, v___x_428_);
v___x_430_ = lean_float_of_nat(v___x_429_);
v___y_416_ = v___x_430_;
goto v___jp_415_;
}
}
v___jp_358_:
{
lean_object* v___x_362_; 
lean_inc(v___y_360_);
v___x_362_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_oldTraces_350_, v_data_361_, v___y_360_, v___y_359_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_363_; 
lean_dec_ref_known(v___x_362_, 1);
v___x_363_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_fst_356_);
return v___x_363_;
}
else
{
lean_dec(v_fst_356_);
return v___x_362_;
}
}
v___jp_368_:
{
uint8_t v_result_371_; lean_object* v___x_372_; lean_object* v___x_373_; double v___x_374_; lean_object* v_data_375_; 
v_result_371_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_fst_356_);
v___x_372_ = lean_box(v_result_371_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
v___x_374_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0);
lean_inc_ref(v_tag_347_);
lean_inc_ref(v___x_373_);
lean_inc(v_cls_345_);
v_data_375_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_375_, 0, v_cls_345_);
lean_ctor_set(v_data_375_, 1, v___x_373_);
lean_ctor_set(v_data_375_, 2, v_tag_347_);
lean_ctor_set_float(v_data_375_, sizeof(void*)*3, v___x_374_);
lean_ctor_set_float(v_data_375_, sizeof(void*)*3 + 8, v___x_374_);
lean_ctor_set_uint8(v_data_375_, sizeof(void*)*3 + 16, v_collapsed_346_);
if (v___x_367_ == 0)
{
lean_dec_ref_known(v___x_373_, 1);
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
lean_dec_ref(v_tag_347_);
lean_dec(v_cls_345_);
v___y_359_ = v_a_370_;
v___y_360_ = v___y_369_;
v_data_361_ = v_data_375_;
goto v___jp_358_;
}
else
{
lean_object* v_data_376_; double v___x_377_; double v___x_378_; 
lean_dec_ref_known(v_data_375_, 3);
v_data_376_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_376_, 0, v_cls_345_);
lean_ctor_set(v_data_376_, 1, v___x_373_);
lean_ctor_set(v_data_376_, 2, v_tag_347_);
v___x_377_ = lean_unbox_float(v_fst_364_);
lean_dec(v_fst_364_);
lean_ctor_set_float(v_data_376_, sizeof(void*)*3, v___x_377_);
v___x_378_ = lean_unbox_float(v_snd_365_);
lean_dec(v_snd_365_);
lean_ctor_set_float(v_data_376_, sizeof(void*)*3 + 8, v___x_378_);
lean_ctor_set_uint8(v_data_376_, sizeof(void*)*3 + 16, v_collapsed_346_);
v___y_359_ = v_a_370_;
v___y_360_ = v___y_369_;
v_data_361_ = v_data_376_;
goto v___jp_358_;
}
}
v___jp_379_:
{
lean_object* v_ref_380_; lean_object* v___x_381_; 
v_ref_380_ = lean_ctor_get(v___y_353_, 2);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v_fst_356_);
v___x_381_ = lean_apply_4(v_msg_351_, v_fst_356_, v___y_353_, v___y_354_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___y_369_ = v_ref_380_;
v_a_370_ = v_a_382_;
goto v___jp_368_;
}
else
{
lean_object* v___x_383_; 
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2);
v___y_369_ = v_ref_380_;
v_a_370_ = v___x_383_;
goto v___jp_368_;
}
}
v___jp_384_:
{
if (v_clsEnabled_349_ == 0)
{
if (v___y_385_ == 0)
{
lean_object* v___x_386_; lean_object* v_traceState_387_; lean_object* v_env_388_; lean_object* v_nextMacroScope_389_; lean_object* v_ngen_390_; lean_object* v_auxDeclNGen_391_; lean_object* v_cache_392_; lean_object* v_messages_393_; lean_object* v_infoState_394_; lean_object* v_snapshotTasks_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
lean_dec_ref(v_msg_351_);
lean_dec_ref(v_tag_347_);
lean_dec(v_cls_345_);
v___x_386_ = lean_st_ref_take(v___y_354_);
v_traceState_387_ = lean_ctor_get(v___x_386_, 4);
v_env_388_ = lean_ctor_get(v___x_386_, 0);
v_nextMacroScope_389_ = lean_ctor_get(v___x_386_, 1);
v_ngen_390_ = lean_ctor_get(v___x_386_, 2);
v_auxDeclNGen_391_ = lean_ctor_get(v___x_386_, 3);
v_cache_392_ = lean_ctor_get(v___x_386_, 5);
v_messages_393_ = lean_ctor_get(v___x_386_, 6);
v_infoState_394_ = lean_ctor_get(v___x_386_, 7);
v_snapshotTasks_395_ = lean_ctor_get(v___x_386_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_414_ == 0)
{
v___x_397_ = v___x_386_;
v_isShared_398_ = v_isSharedCheck_414_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snapshotTasks_395_);
lean_inc(v_infoState_394_);
lean_inc(v_messages_393_);
lean_inc(v_cache_392_);
lean_inc(v_traceState_387_);
lean_inc(v_auxDeclNGen_391_);
lean_inc(v_ngen_390_);
lean_inc(v_nextMacroScope_389_);
lean_inc(v_env_388_);
lean_dec(v___x_386_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_414_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint64_t v_tid_399_; lean_object* v_traces_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_413_; 
v_tid_399_ = lean_ctor_get_uint64(v_traceState_387_, sizeof(void*)*1);
v_traces_400_ = lean_ctor_get(v_traceState_387_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_traceState_387_);
if (v_isSharedCheck_413_ == 0)
{
v___x_402_ = v_traceState_387_;
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_traces_400_);
lean_dec(v_traceState_387_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_350_, v_traces_400_);
lean_dec_ref(v_traces_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_404_);
lean_ctor_set_uint64(v_reuseFailAlloc_412_, sizeof(void*)*1, v_tid_399_);
v___x_406_ = v_reuseFailAlloc_412_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 4, v___x_406_);
v___x_408_ = v___x_397_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_env_388_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_389_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_390_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_cache_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_395_);
v___x_408_ = v_reuseFailAlloc_411_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_st_ref_put(v___y_354_, v___x_408_);
v___x_410_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_fst_356_);
return v___x_410_;
}
}
}
}
}
else
{
goto v___jp_379_;
}
}
else
{
goto v___jp_379_;
}
}
v___jp_415_:
{
double v___x_417_; double v___x_418_; double v___x_419_; uint8_t v___x_420_; 
v___x_417_ = lean_unbox_float(v_snd_365_);
v___x_418_ = lean_unbox_float(v_fst_364_);
v___x_419_ = lean_float_sub(v___x_417_, v___x_418_);
v___x_420_ = lean_float_decLt(v___y_416_, v___x_419_);
v___y_385_ = v___x_420_;
goto v___jp_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_cls_431_, lean_object* v_collapsed_432_, lean_object* v_tag_433_, lean_object* v_opts_434_, lean_object* v_clsEnabled_435_, lean_object* v_oldTraces_436_, lean_object* v_msg_437_, lean_object* v_resStartStop_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v_collapsed_boxed_442_; uint8_t v_clsEnabled_boxed_443_; lean_object* v_res_444_; 
v_collapsed_boxed_442_ = lean_unbox(v_collapsed_432_);
v_clsEnabled_boxed_443_ = lean_unbox(v_clsEnabled_435_);
v_res_444_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v_cls_431_, v_collapsed_boxed_442_, v_tag_433_, v_opts_434_, v_clsEnabled_boxed_443_, v_oldTraces_436_, v_msg_437_, v_resStartStop_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v_opts_434_);
return v_res_444_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_445_; double v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1000000000u);
v___x_446_ = lean_float_of_nat(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_452_, uint8_t v___x_453_, lean_object* v___x_454_, lean_object* v___f_455_, lean_object* v_declNames_456_, lean_object* v___x_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_toCold_462_; lean_object* v_currRecDepth_463_; lean_object* v_ref_464_; uint8_t v_suppressElabErrors_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_622_; 
v___x_461_ = lean_st_ref_get(v___y_459_);
v_toCold_462_ = lean_ctor_get(v___y_458_, 0);
v_currRecDepth_463_ = lean_ctor_get(v___y_458_, 1);
v_ref_464_ = lean_ctor_get(v___y_458_, 2);
v_suppressElabErrors_465_ = lean_ctor_get_uint8(v___y_458_, sizeof(void*)*3 + 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_458_);
if (v_isSharedCheck_622_ == 0)
{
v___x_467_ = v___y_458_;
v_isShared_468_ = v_isSharedCheck_622_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_ref_464_);
lean_inc(v_currRecDepth_463_);
lean_inc(v_toCold_462_);
lean_dec(v___y_458_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_622_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_fileName_469_; lean_object* v_fileMap_470_; lean_object* v_options_471_; lean_object* v_currNamespace_472_; lean_object* v_openDecls_473_; lean_object* v_initHeartbeats_474_; lean_object* v_maxHeartbeats_475_; lean_object* v_quotContext_476_; lean_object* v_currMacroScope_477_; lean_object* v_cancelTk_x3f_478_; lean_object* v_inheritedTraceOptions_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_620_; 
v_fileName_469_ = lean_ctor_get(v_toCold_462_, 0);
v_fileMap_470_ = lean_ctor_get(v_toCold_462_, 1);
v_options_471_ = lean_ctor_get(v_toCold_462_, 2);
v_currNamespace_472_ = lean_ctor_get(v_toCold_462_, 4);
v_openDecls_473_ = lean_ctor_get(v_toCold_462_, 5);
v_initHeartbeats_474_ = lean_ctor_get(v_toCold_462_, 6);
v_maxHeartbeats_475_ = lean_ctor_get(v_toCold_462_, 7);
v_quotContext_476_ = lean_ctor_get(v_toCold_462_, 8);
v_currMacroScope_477_ = lean_ctor_get(v_toCold_462_, 9);
v_cancelTk_x3f_478_ = lean_ctor_get(v_toCold_462_, 10);
v_inheritedTraceOptions_479_ = lean_ctor_get(v_toCold_462_, 11);
v_isSharedCheck_620_ = !lean_is_exclusive(v_toCold_462_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_toCold_462_, 3);
lean_dec(v_unused_621_);
v___x_481_ = v_toCold_462_;
v_isShared_482_ = v_isSharedCheck_620_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_inheritedTraceOptions_479_);
lean_inc(v_cancelTk_x3f_478_);
lean_inc(v_currMacroScope_477_);
lean_inc(v_quotContext_476_);
lean_inc(v_maxHeartbeats_475_);
lean_inc(v_initHeartbeats_474_);
lean_inc(v_openDecls_473_);
lean_inc(v_currNamespace_472_);
lean_inc(v_options_471_);
lean_inc(v_fileMap_470_);
lean_inc(v_fileName_469_);
lean_dec(v_toCold_462_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_620_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_env_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; lean_object* v___y_492_; lean_object* v_a_493_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; uint8_t v___y_509_; lean_object* v___y_510_; lean_object* v_a_511_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v_fileName_567_; lean_object* v_fileMap_568_; lean_object* v_currNamespace_569_; lean_object* v_openDecls_570_; lean_object* v_initHeartbeats_571_; lean_object* v_maxHeartbeats_572_; lean_object* v_quotContext_573_; lean_object* v_currMacroScope_574_; lean_object* v_cancelTk_x3f_575_; lean_object* v_inheritedTraceOptions_576_; lean_object* v_currRecDepth_577_; lean_object* v_ref_578_; uint8_t v_suppressElabErrors_579_; lean_object* v___y_580_; uint8_t v___y_598_; uint8_t v___x_619_; 
v_env_483_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_483_);
lean_dec(v___x_461_);
v___x_484_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_485_ = 0;
v___x_486_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_options_471_, v___x_484_, v___x_485_);
v___x_564_ = l_Lean_diagnostics;
v___x_565_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_486_, v___x_564_);
v___x_619_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_483_);
lean_dec_ref(v_env_483_);
if (v___x_565_ == 0)
{
if (v___x_619_ == 0)
{
v_fileName_567_ = v_fileName_469_;
v_fileMap_568_ = v_fileMap_470_;
v_currNamespace_569_ = v_currNamespace_472_;
v_openDecls_570_ = v_openDecls_473_;
v_initHeartbeats_571_ = v_initHeartbeats_474_;
v_maxHeartbeats_572_ = v_maxHeartbeats_475_;
v_quotContext_573_ = v_quotContext_476_;
v_currMacroScope_574_ = v_currMacroScope_477_;
v_cancelTk_x3f_575_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_576_ = v_inheritedTraceOptions_479_;
v_currRecDepth_577_ = v_currRecDepth_463_;
v_ref_578_ = v_ref_464_;
v_suppressElabErrors_579_ = v_suppressElabErrors_465_;
v___y_580_ = v___y_459_;
goto v___jp_566_;
}
else
{
v___y_598_ = v___x_565_;
goto v___jp_597_;
}
}
else
{
v___y_598_ = v___x_619_;
goto v___jp_597_;
}
v___jp_487_:
{
lean_object* v___x_494_; double v___x_495_; double v___x_496_; double v___x_497_; double v___x_498_; double v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_494_ = lean_io_mono_nanos_now();
v___x_495_ = lean_float_of_nat(v___y_489_);
v___x_496_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_497_ = lean_float_div(v___x_495_, v___x_496_);
v___x_498_ = lean_float_of_nat(v___x_494_);
v___x_499_ = lean_float_div(v___x_498_, v___x_496_);
v___x_500_ = lean_box_float(v___x_497_);
v___x_501_ = lean_box_float(v___x_499_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_a_493_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_452_, v___x_453_, v___x_454_, v___x_486_, v___y_491_, v___y_492_, v___f_455_, v___x_503_, v___y_490_, v___y_488_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v___x_486_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_512_; double v___x_513_; double v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_512_ = lean_io_get_num_heartbeats();
v___x_513_ = lean_float_of_nat(v___y_507_);
v___x_514_ = lean_float_of_nat(v___x_512_);
v___x_515_ = lean_box_float(v___x_513_);
v___x_516_ = lean_box_float(v___x_514_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_511_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_452_, v___x_453_, v___x_454_, v___x_486_, v___y_509_, v___y_510_, v___f_455_, v___x_518_, v___y_508_, v___y_506_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v___x_486_);
return v___x_519_;
}
v___jp_520_:
{
lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_524_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_521_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = l_Lean_trace_profiler_useHeartbeats;
v___x_527_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_486_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_io_mono_nanos_now();
v___x_529_ = l_Lean_Compiler_LCNF_main(v_declNames_456_, v___x_457_, v___y_523_, v___y_521_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 1);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
v___y_488_ = v___y_521_;
v___y_489_ = v___x_528_;
v___y_490_ = v___y_523_;
v___y_491_ = v___y_522_;
v___y_492_ = v_a_525_;
v_a_493_ = v___x_535_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_a_538_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_529_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_529_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 0);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
v___y_488_ = v___y_521_;
v___y_489_ = v___x_528_;
v___y_490_ = v___y_523_;
v___y_491_ = v___y_522_;
v___y_492_ = v_a_525_;
v_a_493_ = v___x_543_;
goto v___jp_487_;
}
}
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_io_get_num_heartbeats();
v___x_547_ = l_Lean_Compiler_LCNF_main(v_declNames_456_, v___x_457_, v___y_523_, v___y_521_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 1);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v___y_506_ = v___y_521_;
v___y_507_ = v___x_546_;
v___y_508_ = v___y_523_;
v___y_509_ = v___y_522_;
v___y_510_ = v_a_525_;
v_a_511_ = v___x_553_;
goto v___jp_505_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_506_ = v___y_521_;
v___y_507_ = v___x_546_;
v___y_508_ = v___y_523_;
v___y_509_ = v___y_522_;
v___y_510_ = v_a_525_;
v_a_511_ = v___x_561_;
goto v___jp_505_;
}
}
}
}
}
v___jp_566_:
{
uint8_t v_hasTrace_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_hasTrace_581_ = lean_ctor_get_uint8(v___x_486_, sizeof(void*)*1);
v___x_582_ = l_Lean_maxRecDepth;
v___x_583_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___x_486_, v___x_582_);
lean_inc_ref(v_inheritedTraceOptions_576_);
lean_inc_ref(v___x_486_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 11, v_inheritedTraceOptions_576_);
lean_ctor_set(v___x_481_, 10, v_cancelTk_x3f_575_);
lean_ctor_set(v___x_481_, 9, v_currMacroScope_574_);
lean_ctor_set(v___x_481_, 8, v_quotContext_573_);
lean_ctor_set(v___x_481_, 7, v_maxHeartbeats_572_);
lean_ctor_set(v___x_481_, 6, v_initHeartbeats_571_);
lean_ctor_set(v___x_481_, 5, v_openDecls_570_);
lean_ctor_set(v___x_481_, 4, v_currNamespace_569_);
lean_ctor_set(v___x_481_, 3, v___x_583_);
lean_ctor_set(v___x_481_, 2, v___x_486_);
lean_ctor_set(v___x_481_, 1, v_fileMap_568_);
lean_ctor_set(v___x_481_, 0, v_fileName_567_);
v___x_585_ = v___x_481_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_fileName_567_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_fileMap_568_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_currNamespace_569_);
lean_ctor_set(v_reuseFailAlloc_596_, 5, v_openDecls_570_);
lean_ctor_set(v_reuseFailAlloc_596_, 6, v_initHeartbeats_571_);
lean_ctor_set(v_reuseFailAlloc_596_, 7, v_maxHeartbeats_572_);
lean_ctor_set(v_reuseFailAlloc_596_, 8, v_quotContext_573_);
lean_ctor_set(v_reuseFailAlloc_596_, 9, v_currMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_596_, 10, v_cancelTk_x3f_575_);
lean_ctor_set(v_reuseFailAlloc_596_, 11, v_inheritedTraceOptions_576_);
v___x_585_ = v_reuseFailAlloc_596_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 2, v_ref_578_);
lean_ctor_set(v___x_467_, 1, v_currRecDepth_577_);
lean_ctor_set(v___x_467_, 0, v___x_585_);
v___x_587_ = v___x_467_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_currRecDepth_577_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ref_578_);
v___x_587_ = v_reuseFailAlloc_595_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*3, v___x_565_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*3 + 1, v_suppressElabErrors_579_);
if (v_hasTrace_581_ == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_inheritedTraceOptions_576_);
lean_dec_ref(v___x_486_);
lean_dec_ref(v___f_455_);
lean_dec_ref(v___x_454_);
lean_dec(v___x_452_);
v___x_588_ = l_Lean_Compiler_LCNF_main(v_declNames_456_, v___x_457_, v___x_587_, v___y_580_);
lean_dec_ref(v___x_587_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
lean_inc(v___x_452_);
v___x_590_ = l_Lean_Name_append(v___x_589_, v___x_452_);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_576_, v___x_486_, v___x_590_);
lean_dec(v___x_590_);
lean_dec_ref(v_inheritedTraceOptions_576_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = l_Lean_trace_profiler;
v___x_593_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_486_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref(v___x_486_);
lean_dec_ref(v___f_455_);
lean_dec_ref(v___x_454_);
lean_dec(v___x_452_);
v___x_594_ = l_Lean_Compiler_LCNF_main(v_declNames_456_, v___x_457_, v___x_587_, v___y_580_);
lean_dec_ref(v___x_587_);
return v___x_594_;
}
else
{
v___y_521_ = v___y_580_;
v___y_522_ = v___x_591_;
v___y_523_ = v___x_587_;
goto v___jp_520_;
}
}
else
{
v___y_521_ = v___y_580_;
v___y_522_ = v___x_591_;
v___y_523_ = v___x_587_;
goto v___jp_520_;
}
}
}
}
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_traceState_604_; lean_object* v_messages_605_; lean_object* v_infoState_606_; lean_object* v_snapshotTasks_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
v___x_599_ = lean_st_ref_take(v___y_459_);
v_env_600_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_599_, 1);
v_ngen_602_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_599_, 3);
v_traceState_604_ = lean_ctor_get(v___x_599_, 4);
v_messages_605_ = lean_ctor_get(v___x_599_, 6);
v_infoState_606_ = lean_ctor_get(v___x_599_, 7);
v_snapshotTasks_607_ = lean_ctor_get(v___x_599_, 8);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_599_, 5);
lean_dec(v_unused_618_);
v___x_609_ = v___x_599_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snapshotTasks_607_);
lean_inc(v_infoState_606_);
lean_inc(v_messages_605_);
lean_inc(v_traceState_604_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_599_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = l_Lean_Kernel_enableDiag(v_env_600_, v___x_565_);
v___x_612_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__3, &l_Lean_Compiler_compile___lam__1___closed__3_once, _init_l_Lean_Compiler_compile___lam__1___closed__3);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 5, v___x_612_);
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_messages_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_infoState_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_snapshotTasks_607_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_st_ref_put(v___y_459_, v___x_614_);
v_fileName_567_ = v_fileName_469_;
v_fileMap_568_ = v_fileMap_470_;
v_currNamespace_569_ = v_currNamespace_472_;
v_openDecls_570_ = v_openDecls_473_;
v_initHeartbeats_571_ = v_initHeartbeats_474_;
v_maxHeartbeats_572_ = v_maxHeartbeats_475_;
v_quotContext_573_ = v_quotContext_476_;
v_currMacroScope_574_ = v_currMacroScope_477_;
v_cancelTk_x3f_575_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_576_ = v_inheritedTraceOptions_479_;
v_currRecDepth_577_ = v_currRecDepth_463_;
v_ref_578_ = v_ref_464_;
v_suppressElabErrors_579_ = v_suppressElabErrors_465_;
v___y_580_ = v___y_459_;
goto v___jp_566_;
}
}
}
else
{
v_fileName_567_ = v_fileName_469_;
v_fileMap_568_ = v_fileMap_470_;
v_currNamespace_569_ = v_currNamespace_472_;
v_openDecls_570_ = v_openDecls_473_;
v_initHeartbeats_571_ = v_initHeartbeats_474_;
v_maxHeartbeats_572_ = v_maxHeartbeats_475_;
v_quotContext_573_ = v_quotContext_476_;
v_currMacroScope_574_ = v_currMacroScope_477_;
v_cancelTk_x3f_575_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_576_ = v_inheritedTraceOptions_479_;
v_currRecDepth_577_ = v_currRecDepth_463_;
v_ref_578_ = v_ref_464_;
v_suppressElabErrors_579_ = v_suppressElabErrors_465_;
v___y_580_ = v___y_459_;
goto v___jp_566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_623_, lean_object* v___x_624_, lean_object* v___x_625_, lean_object* v___f_626_, lean_object* v_declNames_627_, lean_object* v___x_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_6937__boxed_632_; lean_object* v_res_633_; 
v___x_6937__boxed_632_ = lean_unbox(v___x_624_);
v_res_633_ = l_Lean_Compiler_compile___lam__1(v___x_623_, v___x_6937__boxed_632_, v___x_625_, v___f_626_, v_declNames_627_, v___x_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_toCold_643_; lean_object* v_options_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_toCold_643_ = lean_ctor_get(v_a_640_, 0);
v_options_644_ = lean_ctor_get(v_toCold_643_, 2);
lean_inc_ref(v_declNames_639_);
v___f_645_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_645_, 0, v_declNames_639_);
v___x_646_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_647_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_648_ = l_Lean_Options_empty;
v___x_649_ = 1;
v___x_650_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_651_ = lean_box(v___x_649_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_652_, 0, v___x_647_);
lean_closure_set(v___f_652_, 1, v___x_651_);
lean_closure_set(v___f_652_, 2, v___x_650_);
lean_closure_set(v___f_652_, 3, v___f_645_);
lean_closure_set(v___f_652_, 4, v_declNames_639_);
lean_closure_set(v___f_652_, 5, v___x_648_);
v___x_653_ = lean_box(0);
v___x_654_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_646_, v_options_644_, v___f_652_, v___x_653_, v_a_640_, v_a_641_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Compiler_compile(v_declNames_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object* v_00_u03b1_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_x_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object* v_00_u03b1_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_00_u03b1_666_, v_x_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_733_ = 0;
v___x_734_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_735_ = l_Lean_registerTraceClass(v___x_732_, v___x_733_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref_known(v___x_735_, 1);
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_737_ = l_Lean_registerTraceClass(v___x_736_, v___x_733_, v___x_734_);
return v___x_737_;
}
else
{
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_739_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

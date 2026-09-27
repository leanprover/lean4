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
lean_object* l_Lean_Compiler_LCNF_main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Compiler_compile___lam__1___closed__0;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__1;
static lean_once_cell_t l_Lean_Compiler_compile___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_compile___lam__1___closed__2;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 3)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_15_ = ((size_t)5ULL);
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_unsigned_to_nat(32u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__0);
v___x_20_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_16_);
lean_ctor_set(v___x_20_, 3, v___x_16_);
lean_ctor_set_usize(v___x_20_, 4, v___x_15_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; lean_object* v_traceState_24_; lean_object* v_traces_25_; lean_object* v___x_26_; lean_object* v_traceState_27_; lean_object* v_env_28_; lean_object* v_nextMacroScope_29_; lean_object* v_ngen_30_; lean_object* v_auxDeclNGen_31_; lean_object* v_cache_32_; lean_object* v_recordedDeps_33_; lean_object* v_messages_34_; lean_object* v_infoState_35_; lean_object* v_snapshotTasks_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_55_; 
v___x_23_ = lean_st_ref_get(v___y_21_);
v_traceState_24_ = lean_ctor_get(v___x_23_, 4);
lean_inc_ref(v_traceState_24_);
lean_dec(v___x_23_);
v_traces_25_ = lean_ctor_get(v_traceState_24_, 0);
lean_inc_ref(v_traces_25_);
lean_dec_ref(v_traceState_24_);
v___x_26_ = lean_st_ref_take(v___y_21_);
v_traceState_27_ = lean_ctor_get(v___x_26_, 4);
v_env_28_ = lean_ctor_get(v___x_26_, 0);
v_nextMacroScope_29_ = lean_ctor_get(v___x_26_, 1);
v_ngen_30_ = lean_ctor_get(v___x_26_, 2);
v_auxDeclNGen_31_ = lean_ctor_get(v___x_26_, 3);
v_cache_32_ = lean_ctor_get(v___x_26_, 5);
v_recordedDeps_33_ = lean_ctor_get(v___x_26_, 6);
v_messages_34_ = lean_ctor_get(v___x_26_, 7);
v_infoState_35_ = lean_ctor_get(v___x_26_, 8);
v_snapshotTasks_36_ = lean_ctor_get(v___x_26_, 9);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_55_ == 0)
{
v___x_38_ = v___x_26_;
v_isShared_39_ = v_isSharedCheck_55_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_snapshotTasks_36_);
lean_inc(v_infoState_35_);
lean_inc(v_messages_34_);
lean_inc(v_recordedDeps_33_);
lean_inc(v_cache_32_);
lean_inc(v_traceState_27_);
lean_inc(v_auxDeclNGen_31_);
lean_inc(v_ngen_30_);
lean_inc(v_nextMacroScope_29_);
lean_inc(v_env_28_);
lean_dec(v___x_26_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_55_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
uint64_t v_tid_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_53_; 
v_tid_40_ = lean_ctor_get_uint64(v_traceState_27_, sizeof(void*)*1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_traceState_27_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v_traceState_27_, 0);
lean_dec(v_unused_54_);
v___x_42_ = v_traceState_27_;
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
else
{
lean_dec(v_traceState_27_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___closed__1);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_44_);
lean_ctor_set_uint64(v_reuseFailAlloc_52_, sizeof(void*)*1, v_tid_40_);
v___x_46_ = v_reuseFailAlloc_52_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_48_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 4, v___x_46_);
v___x_48_ = v___x_38_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_env_28_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_nextMacroScope_29_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_ngen_30_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_auxDeclNGen_31_);
lean_ctor_set(v_reuseFailAlloc_51_, 4, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_51_, 5, v_cache_32_);
lean_ctor_set(v_reuseFailAlloc_51_, 6, v_recordedDeps_33_);
lean_ctor_set(v_reuseFailAlloc_51_, 7, v_messages_34_);
lean_ctor_set(v_reuseFailAlloc_51_, 8, v_infoState_35_);
lean_ctor_set(v_reuseFailAlloc_51_, 9, v_snapshotTasks_36_);
v___x_48_ = v_reuseFailAlloc_51_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_st_ref_put(v___y_21_, v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v_traces_25_);
return v___x_50_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___boxed(lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___boxed(lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
lean_object* v_name_69_; lean_object* v_defValue_70_; lean_object* v_map_71_; lean_object* v___x_72_; 
v_name_69_ = lean_ctor_get(v_opt_68_, 0);
v_defValue_70_ = lean_ctor_get(v_opt_68_, 1);
v_map_71_ = lean_ctor_get(v_opts_67_, 0);
v___x_72_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_71_, v_name_69_);
if (lean_obj_tag(v___x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = lean_unbox(v_defValue_70_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; 
v_val_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v___x_72_, 1);
if (lean_obj_tag(v_val_74_) == 1)
{
uint8_t v_v_75_; 
v_v_75_ = lean_ctor_get_uint8(v_val_74_, 0);
lean_dec_ref_known(v_val_74_, 0);
return v_v_75_;
}
else
{
uint8_t v___x_76_; 
lean_dec(v_val_74_);
v___x_76_ = lean_unbox(v_defValue_70_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_77_, v_opt_78_);
lean_dec_ref(v_opt_78_);
lean_dec_ref(v_opts_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(lean_object* v_e_151_){
_start:
{
if (lean_obj_tag(v_e_151_) == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 2;
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___boxed(lean_object* v_e_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_e_154_);
lean_dec_ref(v_e_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v_x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v_x_157_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v_x_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 1);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v_x_157_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v_x_157_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v_x_157_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 0);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg___boxed(lean_object* v_x_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(size_t v_sz_178_, size_t v_i_179_, lean_object* v_bs_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_181_ == 0)
{
return v_bs_180_;
}
else
{
lean_object* v_v_182_; lean_object* v_msg_183_; lean_object* v___x_184_; lean_object* v_bs_x27_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v___x_188_; 
v_v_182_ = lean_array_uget_borrowed(v_bs_180_, v_i_179_);
v_msg_183_ = lean_ctor_get(v_v_182_, 1);
lean_inc_ref(v_msg_183_);
v___x_184_ = lean_unsigned_to_nat(0u);
v_bs_x27_185_ = lean_array_uset(v_bs_180_, v_i_179_, v___x_184_);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_i_179_, v___x_186_);
v___x_188_ = lean_array_uset(v_bs_x27_185_, v_i_179_, v_msg_183_);
v_i_179_ = v___x_187_;
v_bs_180_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6___boxed(lean_object* v_sz_190_, lean_object* v_i_191_, lean_object* v_bs_192_){
_start:
{
size_t v_sz_boxed_193_; size_t v_i_boxed_194_; lean_object* v_res_195_; 
v_sz_boxed_193_ = lean_unbox_usize(v_sz_190_);
lean_dec(v_sz_190_);
v_i_boxed_194_ = lean_unbox_usize(v_i_191_);
lean_dec(v_i_191_);
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_boxed_193_, v_i_boxed_194_, v_bs_192_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v___x_200_);
lean_ctor_set(v___x_201_, 4, v___x_199_);
lean_ctor_set(v___x_201_, 5, v___x_199_);
lean_ctor_set(v___x_201_, 6, v___x_199_);
lean_ctor_set(v___x_201_, 7, v___x_199_);
lean_ctor_set(v___x_201_, 8, v___x_199_);
lean_ctor_set(v___x_201_, 9, v___x_199_);
lean_ctor_set(v___x_201_, 10, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4(void){
_start:
{
size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_205_ = ((size_t)5ULL);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_unsigned_to_nat(32u);
v___x_208_ = lean_mk_empty_array_with_capacity(v___x_207_);
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3);
v___x_210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_206_);
lean_ctor_set(v___x_210_, 3, v___x_206_);
lean_ctor_set_usize(v___x_210_, 4, v___x_205_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(1);
v___x_212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4);
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_211_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_toCold_220_; lean_object* v_env_221_; lean_object* v_options_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_219_ = lean_st_ref_get(v___y_217_);
v_toCold_220_ = lean_ctor_get(v___y_216_, 0);
v_env_221_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_env_221_);
lean_dec(v___x_219_);
v_options_222_ = lean_ctor_get(v_toCold_220_, 2);
v___x_223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2);
v___x_224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5);
lean_inc_ref(v_options_222_);
v___x_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_225_, 0, v_env_221_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
lean_ctor_set(v___x_225_, 3, v_options_222_);
v___x_226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_msgData_215_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___boxed(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msgData_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object* v_oldTraces_233_, lean_object* v_data_234_, lean_object* v_ref_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_toCold_240_; lean_object* v_currRecDepth_241_; lean_object* v_ref_242_; uint16_t v_optionFlags_243_; uint8_t v_suppressElabErrors_244_; uint8_t v_isRecordingDeps_245_; lean_object* v_ref_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_traceState_249_; lean_object* v_traces_250_; lean_object* v___x_251_; size_t v_sz_252_; size_t v___x_253_; lean_object* v___x_254_; lean_object* v_msg_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_295_; 
v_toCold_240_ = lean_ctor_get(v___y_237_, 0);
v_currRecDepth_241_ = lean_ctor_get(v___y_237_, 1);
v_ref_242_ = lean_ctor_get(v___y_237_, 2);
v_optionFlags_243_ = lean_ctor_get_uint16(v___y_237_, sizeof(void*)*3);
v_suppressElabErrors_244_ = lean_ctor_get_uint8(v___y_237_, sizeof(void*)*3 + 2);
v_isRecordingDeps_245_ = lean_ctor_get_uint8(v___y_237_, sizeof(void*)*3 + 3);
v_ref_246_ = l_Lean_replaceRef(v_ref_235_, v_ref_242_);
lean_inc(v_currRecDepth_241_);
lean_inc_ref(v_toCold_240_);
v___x_247_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_247_, 0, v_toCold_240_);
lean_ctor_set(v___x_247_, 1, v_currRecDepth_241_);
lean_ctor_set(v___x_247_, 2, v_ref_246_);
lean_ctor_set_uint16(v___x_247_, sizeof(void*)*3, v_optionFlags_243_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*3 + 2, v_suppressElabErrors_244_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*3 + 3, v_isRecordingDeps_245_);
v___x_248_ = lean_st_ref_get(v___y_238_);
v_traceState_249_ = lean_ctor_get(v___x_248_, 4);
lean_inc_ref(v_traceState_249_);
lean_dec(v___x_248_);
v_traces_250_ = lean_ctor_get(v_traceState_249_, 0);
lean_inc_ref(v_traces_250_);
lean_dec_ref(v_traceState_249_);
v___x_251_ = l_Lean_PersistentArray_toArray___redArg(v_traces_250_);
lean_dec_ref(v_traces_250_);
v_sz_252_ = lean_array_size(v___x_251_);
v___x_253_ = ((size_t)0ULL);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_252_, v___x_253_, v___x_251_);
v_msg_255_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_255_, 0, v_data_234_);
lean_ctor_set(v_msg_255_, 1, v_msg_236_);
lean_ctor_set(v_msg_255_, 2, v___x_254_);
v___x_256_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msg_255_, v___x_247_, v___y_238_);
lean_dec_ref_known(v___x_247_, 3);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_295_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_295_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_295_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v_traceState_262_; lean_object* v_env_263_; lean_object* v_nextMacroScope_264_; lean_object* v_ngen_265_; lean_object* v_auxDeclNGen_266_; lean_object* v_cache_267_; lean_object* v_recordedDeps_268_; lean_object* v_messages_269_; lean_object* v_infoState_270_; lean_object* v_snapshotTasks_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v___x_261_ = lean_st_ref_take(v___y_238_);
v_traceState_262_ = lean_ctor_get(v___x_261_, 4);
v_env_263_ = lean_ctor_get(v___x_261_, 0);
v_nextMacroScope_264_ = lean_ctor_get(v___x_261_, 1);
v_ngen_265_ = lean_ctor_get(v___x_261_, 2);
v_auxDeclNGen_266_ = lean_ctor_get(v___x_261_, 3);
v_cache_267_ = lean_ctor_get(v___x_261_, 5);
v_recordedDeps_268_ = lean_ctor_get(v___x_261_, 6);
v_messages_269_ = lean_ctor_get(v___x_261_, 7);
v_infoState_270_ = lean_ctor_get(v___x_261_, 8);
v_snapshotTasks_271_ = lean_ctor_get(v___x_261_, 9);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v___x_261_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snapshotTasks_271_);
lean_inc(v_infoState_270_);
lean_inc(v_messages_269_);
lean_inc(v_recordedDeps_268_);
lean_inc(v_cache_267_);
lean_inc(v_traceState_262_);
lean_inc(v_auxDeclNGen_266_);
lean_inc(v_ngen_265_);
lean_inc(v_nextMacroScope_264_);
lean_inc(v_env_263_);
lean_dec(v___x_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint64_t v_tid_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_292_; 
v_tid_275_ = lean_ctor_get_uint64(v_traceState_262_, sizeof(void*)*1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_traceState_262_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_traceState_262_, 0);
lean_dec(v_unused_293_);
v___x_277_ = v_traceState_262_;
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
else
{
lean_dec(v_traceState_262_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_ref_235_);
lean_ctor_set(v___x_280_, 1, v_a_257_);
v___x_281_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_233_, v___x_280_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_281_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_281_);
lean_ctor_set_uint64(v_reuseFailAlloc_291_, sizeof(void*)*1, v_tid_275_);
v___x_283_ = v_reuseFailAlloc_291_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v___x_283_);
v___x_285_ = v___x_273_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_env_263_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_nextMacroScope_264_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_ngen_265_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_auxDeclNGen_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_cache_267_);
lean_ctor_set(v_reuseFailAlloc_290_, 6, v_recordedDeps_268_);
lean_ctor_set(v_reuseFailAlloc_290_, 7, v_messages_269_);
lean_ctor_set(v_reuseFailAlloc_290_, 8, v_infoState_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 9, v_snapshotTasks_271_);
v___x_285_ = v_reuseFailAlloc_290_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_st_ref_put(v___y_238_, v___x_285_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_279_);
v___x_288_ = v___x_259_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_279_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object* v_oldTraces_296_, lean_object* v_data_297_, lean_object* v_ref_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_296_, v_data_297_, v_ref_298_, v_msg_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0(void){
_start:
{
lean_object* v___x_304_; double v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_float_of_nat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3(void){
_start:
{
lean_object* v___x_309_; double v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1000u);
v___x_310_ = lean_float_of_nat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_311_, uint8_t v_collapsed_312_, lean_object* v_tag_313_, lean_object* v_opts_314_, uint8_t v_clsEnabled_315_, lean_object* v_oldTraces_316_, lean_object* v_msg_317_, lean_object* v_resStartStop_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v_data_327_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___y_335_; lean_object* v_a_336_; uint8_t v___y_351_; double v___y_383_; 
v_fst_322_ = lean_ctor_get(v_resStartStop_318_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v_resStartStop_318_, 1);
lean_inc(v_snd_323_);
lean_dec_ref(v_resStartStop_318_);
v_fst_330_ = lean_ctor_get(v_snd_323_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v_snd_323_, 1);
lean_inc(v_snd_331_);
lean_dec(v_snd_323_);
v___x_332_ = l_Lean_trace_profiler;
v___x_333_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_314_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_351_ = v___x_333_;
goto v___jp_350_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = l_Lean_trace_profiler_useHeartbeats;
v___x_389_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_314_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; double v___x_392_; double v___x_393_; double v___x_394_; 
v___x_390_ = l_Lean_trace_profiler_threshold;
v___x_391_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_314_, v___x_390_);
v___x_392_ = lean_float_of_nat(v___x_391_);
v___x_393_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3);
v___x_394_ = lean_float_div(v___x_392_, v___x_393_);
v___y_383_ = v___x_394_;
goto v___jp_382_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; double v___x_397_; 
v___x_395_ = l_Lean_trace_profiler_threshold;
v___x_396_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_314_, v___x_395_);
v___x_397_ = lean_float_of_nat(v___x_396_);
v___y_383_ = v___x_397_;
goto v___jp_382_;
}
}
v___jp_324_:
{
lean_object* v___x_328_; 
lean_inc(v___y_326_);
v___x_328_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_316_, v_data_327_, v___y_326_, v___y_325_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_322_);
return v___x_329_;
}
else
{
lean_dec(v_fst_322_);
return v___x_328_;
}
}
v___jp_334_:
{
uint8_t v_result_337_; lean_object* v___x_338_; lean_object* v___x_339_; double v___x_340_; lean_object* v_data_341_; 
v_result_337_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_fst_322_);
v___x_338_ = lean_box(v_result_337_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0);
lean_inc_ref(v_tag_313_);
lean_inc_ref(v___x_339_);
lean_inc(v_cls_311_);
v_data_341_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_341_, 0, v_cls_311_);
lean_ctor_set(v_data_341_, 1, v___x_339_);
lean_ctor_set(v_data_341_, 2, v_tag_313_);
lean_ctor_set_float(v_data_341_, sizeof(void*)*3, v___x_340_);
lean_ctor_set_float(v_data_341_, sizeof(void*)*3 + 8, v___x_340_);
lean_ctor_set_uint8(v_data_341_, sizeof(void*)*3 + 16, v_collapsed_312_);
if (v___x_333_ == 0)
{
lean_dec_ref_known(v___x_339_, 1);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec_ref(v_tag_313_);
lean_dec(v_cls_311_);
v___y_325_ = v_a_336_;
v___y_326_ = v___y_335_;
v_data_327_ = v_data_341_;
goto v___jp_324_;
}
else
{
lean_object* v_data_342_; double v___x_343_; double v___x_344_; 
lean_dec_ref_known(v_data_341_, 3);
v_data_342_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_342_, 0, v_cls_311_);
lean_ctor_set(v_data_342_, 1, v___x_339_);
lean_ctor_set(v_data_342_, 2, v_tag_313_);
v___x_343_ = lean_unbox_float(v_fst_330_);
lean_dec(v_fst_330_);
lean_ctor_set_float(v_data_342_, sizeof(void*)*3, v___x_343_);
v___x_344_ = lean_unbox_float(v_snd_331_);
lean_dec(v_snd_331_);
lean_ctor_set_float(v_data_342_, sizeof(void*)*3 + 8, v___x_344_);
lean_ctor_set_uint8(v_data_342_, sizeof(void*)*3 + 16, v_collapsed_312_);
v___y_325_ = v_a_336_;
v___y_326_ = v___y_335_;
v_data_327_ = v_data_342_;
goto v___jp_324_;
}
}
v___jp_345_:
{
lean_object* v_ref_346_; lean_object* v___x_347_; 
v_ref_346_ = lean_ctor_get(v___y_319_, 2);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v_fst_322_);
v___x_347_ = lean_apply_4(v_msg_317_, v_fst_322_, v___y_319_, v___y_320_, lean_box(0));
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___y_335_ = v_ref_346_;
v_a_336_ = v_a_348_;
goto v___jp_334_;
}
else
{
lean_object* v___x_349_; 
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2);
v___y_335_ = v_ref_346_;
v_a_336_ = v___x_349_;
goto v___jp_334_;
}
}
v___jp_350_:
{
if (v_clsEnabled_315_ == 0)
{
if (v___y_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_traceState_353_; lean_object* v_env_354_; lean_object* v_nextMacroScope_355_; lean_object* v_ngen_356_; lean_object* v_auxDeclNGen_357_; lean_object* v_cache_358_; lean_object* v_recordedDeps_359_; lean_object* v_messages_360_; lean_object* v_infoState_361_; lean_object* v_snapshotTasks_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec_ref(v_msg_317_);
lean_dec_ref(v_tag_313_);
lean_dec(v_cls_311_);
v___x_352_ = lean_st_ref_take(v___y_320_);
v_traceState_353_ = lean_ctor_get(v___x_352_, 4);
v_env_354_ = lean_ctor_get(v___x_352_, 0);
v_nextMacroScope_355_ = lean_ctor_get(v___x_352_, 1);
v_ngen_356_ = lean_ctor_get(v___x_352_, 2);
v_auxDeclNGen_357_ = lean_ctor_get(v___x_352_, 3);
v_cache_358_ = lean_ctor_get(v___x_352_, 5);
v_recordedDeps_359_ = lean_ctor_get(v___x_352_, 6);
v_messages_360_ = lean_ctor_get(v___x_352_, 7);
v_infoState_361_ = lean_ctor_get(v___x_352_, 8);
v_snapshotTasks_362_ = lean_ctor_get(v___x_352_, 9);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_381_ == 0)
{
v___x_364_ = v___x_352_;
v_isShared_365_ = v_isSharedCheck_381_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snapshotTasks_362_);
lean_inc(v_infoState_361_);
lean_inc(v_messages_360_);
lean_inc(v_recordedDeps_359_);
lean_inc(v_cache_358_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_357_);
lean_inc(v_ngen_356_);
lean_inc(v_nextMacroScope_355_);
lean_inc(v_env_354_);
lean_dec(v___x_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_381_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint64_t v_tid_366_; lean_object* v_traces_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_380_; 
v_tid_366_ = lean_ctor_get_uint64(v_traceState_353_, sizeof(void*)*1);
v_traces_367_ = lean_ctor_get(v_traceState_353_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_traceState_353_);
if (v_isSharedCheck_380_ == 0)
{
v___x_369_ = v_traceState_353_;
v_isShared_370_ = v_isSharedCheck_380_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_traces_367_);
lean_dec(v_traceState_353_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_380_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_316_, v_traces_367_);
lean_dec_ref(v_traces_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_371_);
lean_ctor_set_uint64(v_reuseFailAlloc_379_, sizeof(void*)*1, v_tid_366_);
v___x_373_ = v_reuseFailAlloc_379_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v___x_373_);
v___x_375_ = v___x_364_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_env_354_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_nextMacroScope_355_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_ngen_356_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_auxDeclNGen_357_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_cache_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_recordedDeps_359_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_messages_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_infoState_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 9, v_snapshotTasks_362_);
v___x_375_ = v_reuseFailAlloc_378_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_st_ref_put(v___y_320_, v___x_375_);
v___x_377_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_322_);
return v___x_377_;
}
}
}
}
}
else
{
goto v___jp_345_;
}
}
else
{
goto v___jp_345_;
}
}
v___jp_382_:
{
double v___x_384_; double v___x_385_; double v___x_386_; uint8_t v___x_387_; 
v___x_384_ = lean_unbox_float(v_snd_331_);
v___x_385_ = lean_unbox_float(v_fst_330_);
v___x_386_ = lean_float_sub(v___x_384_, v___x_385_);
v___x_387_ = lean_float_decLt(v___y_383_, v___x_386_);
v___y_351_ = v___x_387_;
goto v___jp_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_398_, lean_object* v_collapsed_399_, lean_object* v_tag_400_, lean_object* v_opts_401_, lean_object* v_clsEnabled_402_, lean_object* v_oldTraces_403_, lean_object* v_msg_404_, lean_object* v_resStartStop_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v_collapsed_boxed_409_; uint8_t v_clsEnabled_boxed_410_; lean_object* v_res_411_; 
v_collapsed_boxed_409_ = lean_unbox(v_collapsed_399_);
v_clsEnabled_boxed_410_ = lean_unbox(v_clsEnabled_402_);
v_res_411_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_398_, v_collapsed_boxed_409_, v_tag_400_, v_opts_401_, v_clsEnabled_boxed_410_, v_oldTraces_403_, v_msg_404_, v_resStartStop_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec_ref(v_opts_401_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_o_415_, lean_object* v_k_416_, uint8_t v_v_417_){
_start:
{
lean_object* v_map_418_; uint8_t v_hasTrace_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_433_; 
v_map_418_ = lean_ctor_get(v_o_415_, 0);
v_hasTrace_419_ = lean_ctor_get_uint8(v_o_415_, sizeof(void*)*1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_o_415_);
if (v_isSharedCheck_433_ == 0)
{
v___x_421_ = v_o_415_;
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_map_418_);
lean_dec(v_o_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_423_, 0, v_v_417_);
lean_inc(v_k_416_);
v___x_424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_416_, v___x_423_, v_map_418_);
if (v_hasTrace_419_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_428_; 
v___x_425_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
v___x_426_ = l_Lean_Name_isPrefixOf(v___x_425_, v_k_416_);
lean_dec(v_k_416_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_424_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_424_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_426_);
return v___x_428_;
}
}
else
{
lean_object* v___x_431_; 
lean_dec(v_k_416_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_424_);
v___x_431_ = v___x_421_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*1, v_hasTrace_419_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_o_434_, lean_object* v_k_435_, lean_object* v_v_436_){
_start:
{
uint8_t v_v_boxed_437_; lean_object* v_res_438_; 
v_v_boxed_437_ = lean_unbox(v_v_436_);
v_res_438_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_o_434_, v_k_435_, v_v_boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(lean_object* v_opts_439_, lean_object* v_opt_440_, uint8_t v_val_441_){
_start:
{
lean_object* v_name_442_; lean_object* v___x_443_; 
v_name_442_ = lean_ctor_get(v_opt_440_, 0);
lean_inc(v_name_442_);
lean_dec_ref(v_opt_440_);
v___x_443_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_opts_439_, v_name_442_, v_val_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_opts_444_, lean_object* v_opt_445_, lean_object* v_val_446_){
_start:
{
uint8_t v_val_boxed_447_; lean_object* v_res_448_; 
v_val_boxed_447_ = lean_unbox(v_val_446_);
v_res_448_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_opts_444_, v_opt_445_, v_val_boxed_447_);
return v_res_448_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_449_; double v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(1000000000u);
v___x_450_ = lean_float_of_nat(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_455_, uint8_t v___x_456_, lean_object* v___x_457_, lean_object* v___f_458_, lean_object* v_declNames_459_, lean_object* v___x_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v_a_471_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v_a_487_; lean_object* v___y_500_; uint8_t v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; uint16_t v___y_545_; lean_object* v___y_546_; lean_object* v_fileName_547_; lean_object* v_fileMap_548_; lean_object* v_currNamespace_549_; lean_object* v_openDecls_550_; lean_object* v_initHeartbeats_551_; lean_object* v_maxHeartbeats_552_; lean_object* v_quotContext_553_; lean_object* v_currMacroScope_554_; lean_object* v_cancelTk_x3f_555_; lean_object* v_inheritedTraceOptions_556_; lean_object* v_currRecDepth_557_; lean_object* v_ref_558_; uint8_t v_suppressElabErrors_559_; uint8_t v_isRecordingDeps_560_; lean_object* v___y_561_; lean_object* v_toCold_574_; lean_object* v_currRecDepth_575_; lean_object* v_ref_576_; uint8_t v_suppressElabErrors_577_; uint8_t v_isRecordingDeps_578_; lean_object* v_fileName_579_; lean_object* v_fileMap_580_; lean_object* v_options_581_; lean_object* v_currNamespace_582_; lean_object* v_openDecls_583_; lean_object* v_initHeartbeats_584_; lean_object* v_maxHeartbeats_585_; lean_object* v_quotContext_586_; lean_object* v_currMacroScope_587_; lean_object* v_cancelTk_x3f_588_; lean_object* v_inheritedTraceOptions_589_; uint16_t v___y_591_; uint8_t v___y_592_; lean_object* v___y_593_; lean_object* v___y_616_; 
v_toCold_574_ = lean_ctor_get(v___y_461_, 0);
lean_inc_ref(v_toCold_574_);
v_currRecDepth_575_ = lean_ctor_get(v___y_461_, 1);
lean_inc(v_currRecDepth_575_);
v_ref_576_ = lean_ctor_get(v___y_461_, 2);
lean_inc(v_ref_576_);
v_suppressElabErrors_577_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*3 + 2);
v_isRecordingDeps_578_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_461_);
v_fileName_579_ = lean_ctor_get(v_toCold_574_, 0);
lean_inc_ref(v_fileName_579_);
v_fileMap_580_ = lean_ctor_get(v_toCold_574_, 1);
lean_inc_ref(v_fileMap_580_);
v_options_581_ = lean_ctor_get(v_toCold_574_, 2);
lean_inc_ref(v_options_581_);
v_currNamespace_582_ = lean_ctor_get(v_toCold_574_, 4);
lean_inc(v_currNamespace_582_);
v_openDecls_583_ = lean_ctor_get(v_toCold_574_, 5);
lean_inc(v_openDecls_583_);
v_initHeartbeats_584_ = lean_ctor_get(v_toCold_574_, 6);
lean_inc(v_initHeartbeats_584_);
v_maxHeartbeats_585_ = lean_ctor_get(v_toCold_574_, 7);
lean_inc(v_maxHeartbeats_585_);
v_quotContext_586_ = lean_ctor_get(v_toCold_574_, 8);
lean_inc(v_quotContext_586_);
v_currMacroScope_587_ = lean_ctor_get(v_toCold_574_, 9);
lean_inc(v_currMacroScope_587_);
v_cancelTk_x3f_588_ = lean_ctor_get(v_toCold_574_, 10);
lean_inc(v_cancelTk_x3f_588_);
v_inheritedTraceOptions_589_ = lean_ctor_get(v_toCold_574_, 11);
lean_inc_ref(v_inheritedTraceOptions_589_);
lean_dec_ref(v_toCold_574_);
if (v_isRecordingDeps_578_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_627_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_options_581_, v___x_626_, v_isRecordingDeps_578_);
v___y_616_ = v___x_627_;
goto v___jp_615_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_581_);
v___y_616_ = v___x_628_;
goto v___jp_615_;
}
v___jp_464_:
{
lean_object* v___x_472_; double v___x_473_; double v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_472_ = lean_io_get_num_heartbeats();
v___x_473_ = lean_float_of_nat(v___y_465_);
v___x_474_ = lean_float_of_nat(v___x_472_);
v___x_475_ = lean_box_float(v___x_473_);
v___x_476_ = lean_box_float(v___x_474_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_a_471_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_455_, v___x_456_, v___x_457_, v___y_467_, v___y_470_, v___y_466_, v___f_458_, v___x_478_, v___y_469_, v___y_468_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v___y_467_);
return v___x_479_;
}
v___jp_480_:
{
lean_object* v___x_488_; double v___x_489_; double v___x_490_; double v___x_491_; double v___x_492_; double v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_488_ = lean_io_mono_nanos_now();
v___x_489_ = lean_float_of_nat(v___y_482_);
v___x_490_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_491_ = lean_float_div(v___x_489_, v___x_490_);
v___x_492_ = lean_float_of_nat(v___x_488_);
v___x_493_ = lean_float_div(v___x_492_, v___x_490_);
v___x_494_ = lean_box_float(v___x_491_);
v___x_495_ = lean_box_float(v___x_493_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_a_487_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_455_, v___x_456_, v___x_457_, v___y_483_, v___y_486_, v___y_481_, v___f_458_, v___x_497_, v___y_485_, v___y_484_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_483_);
return v___x_498_;
}
v___jp_499_:
{
lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_502_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_507_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_500_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_io_mono_nanos_now();
v___x_509_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___y_503_, v___y_502_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_481_ = v_a_505_;
v___y_482_ = v___x_508_;
v___y_483_ = v___y_500_;
v___y_484_ = v___y_502_;
v___y_485_ = v___y_503_;
v___y_486_ = v___y_501_;
v_a_487_ = v___x_515_;
goto v___jp_480_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
v_a_518_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_509_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_509_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 0);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v___y_481_ = v_a_505_;
v___y_482_ = v___x_508_;
v___y_483_ = v___y_500_;
v___y_484_ = v___y_502_;
v___y_485_ = v___y_503_;
v___y_486_ = v___y_501_;
v_a_487_ = v___x_523_;
goto v___jp_480_;
}
}
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_io_get_num_heartbeats();
v___x_527_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___y_503_, v___y_502_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 1);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_465_ = v___x_526_;
v___y_466_ = v_a_505_;
v___y_467_ = v___y_500_;
v___y_468_ = v___y_502_;
v___y_469_ = v___y_503_;
v___y_470_ = v___y_501_;
v_a_471_ = v___x_533_;
goto v___jp_464_;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_527_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_527_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 0);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v___y_465_ = v___x_526_;
v___y_466_ = v_a_505_;
v___y_467_ = v___y_500_;
v___y_468_ = v___y_502_;
v___y_469_ = v___y_503_;
v___y_470_ = v___y_501_;
v_a_471_ = v___x_541_;
goto v___jp_464_;
}
}
}
}
}
v___jp_544_:
{
uint8_t v_hasTrace_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_hasTrace_562_ = lean_ctor_get_uint8(v___y_546_, sizeof(void*)*1);
v___x_563_ = l_Lean_maxRecDepth;
v___x_564_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v___y_546_, v___x_563_);
lean_inc_ref(v_inheritedTraceOptions_556_);
lean_inc_ref(v___y_546_);
v___x_565_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_565_, 0, v_fileName_547_);
lean_ctor_set(v___x_565_, 1, v_fileMap_548_);
lean_ctor_set(v___x_565_, 2, v___y_546_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
lean_ctor_set(v___x_565_, 4, v_currNamespace_549_);
lean_ctor_set(v___x_565_, 5, v_openDecls_550_);
lean_ctor_set(v___x_565_, 6, v_initHeartbeats_551_);
lean_ctor_set(v___x_565_, 7, v_maxHeartbeats_552_);
lean_ctor_set(v___x_565_, 8, v_quotContext_553_);
lean_ctor_set(v___x_565_, 9, v_currMacroScope_554_);
lean_ctor_set(v___x_565_, 10, v_cancelTk_x3f_555_);
lean_ctor_set(v___x_565_, 11, v_inheritedTraceOptions_556_);
v___x_566_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v_currRecDepth_557_);
lean_ctor_set(v___x_566_, 2, v_ref_558_);
lean_ctor_set_uint16(v___x_566_, sizeof(void*)*3, v___y_545_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*3 + 2, v_suppressElabErrors_559_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*3 + 3, v_isRecordingDeps_560_);
if (v_hasTrace_562_ == 0)
{
lean_object* v___x_567_; 
lean_dec_ref(v_inheritedTraceOptions_556_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v___f_458_);
lean_dec_ref(v___x_457_);
lean_dec(v___x_455_);
v___x_567_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___x_566_, v___y_561_);
lean_dec_ref_known(v___x_566_, 3);
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
lean_inc(v___x_455_);
v___x_569_ = l_Lean_Name_append(v___x_568_, v___x_455_);
v___x_570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_556_, v___y_546_, v___x_569_);
lean_dec(v___x_569_);
lean_dec_ref(v_inheritedTraceOptions_556_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = l_Lean_trace_profiler;
v___x_572_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_546_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec_ref(v___y_546_);
lean_dec_ref(v___f_458_);
lean_dec_ref(v___x_457_);
lean_dec(v___x_455_);
v___x_573_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___x_566_, v___y_561_);
lean_dec_ref_known(v___x_566_, 3);
return v___x_573_;
}
else
{
v___y_500_ = v___y_546_;
v___y_501_ = v___x_570_;
v___y_502_ = v___y_561_;
v___y_503_ = v___x_566_;
goto v___jp_499_;
}
}
else
{
v___y_500_ = v___y_546_;
v___y_501_ = v___x_570_;
v___y_502_ = v___y_561_;
v___y_503_ = v___x_566_;
goto v___jp_499_;
}
}
}
v___jp_590_:
{
lean_object* v___x_594_; lean_object* v_env_595_; lean_object* v_nextMacroScope_596_; lean_object* v_ngen_597_; lean_object* v_auxDeclNGen_598_; lean_object* v_traceState_599_; lean_object* v_recordedDeps_600_; lean_object* v_messages_601_; lean_object* v_infoState_602_; lean_object* v_snapshotTasks_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_613_; 
v___x_594_ = lean_st_ref_take(v___y_462_);
v_env_595_ = lean_ctor_get(v___x_594_, 0);
v_nextMacroScope_596_ = lean_ctor_get(v___x_594_, 1);
v_ngen_597_ = lean_ctor_get(v___x_594_, 2);
v_auxDeclNGen_598_ = lean_ctor_get(v___x_594_, 3);
v_traceState_599_ = lean_ctor_get(v___x_594_, 4);
v_recordedDeps_600_ = lean_ctor_get(v___x_594_, 6);
v_messages_601_ = lean_ctor_get(v___x_594_, 7);
v_infoState_602_ = lean_ctor_get(v___x_594_, 8);
v_snapshotTasks_603_ = lean_ctor_get(v___x_594_, 9);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_594_, 5);
lean_dec(v_unused_614_);
v___x_605_ = v___x_594_;
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_snapshotTasks_603_);
lean_inc(v_infoState_602_);
lean_inc(v_messages_601_);
lean_inc(v_recordedDeps_600_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_598_);
lean_inc(v_ngen_597_);
lean_inc(v_nextMacroScope_596_);
lean_inc(v_env_595_);
lean_dec(v___x_594_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = l_Lean_Kernel_enableDiag(v_env_595_, v___y_592_);
v___x_608_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 5, v___x_608_);
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_610_ = v___x_605_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_nextMacroScope_596_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_ngen_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_auxDeclNGen_598_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_traceState_599_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_recordedDeps_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_messages_601_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v_infoState_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 9, v_snapshotTasks_603_);
v___x_610_ = v_reuseFailAlloc_612_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = lean_st_ref_put(v___y_462_, v___x_610_);
v___y_545_ = v___y_591_;
v___y_546_ = v___y_593_;
v_fileName_547_ = v_fileName_579_;
v_fileMap_548_ = v_fileMap_580_;
v_currNamespace_549_ = v_currNamespace_582_;
v_openDecls_550_ = v_openDecls_583_;
v_initHeartbeats_551_ = v_initHeartbeats_584_;
v_maxHeartbeats_552_ = v_maxHeartbeats_585_;
v_quotContext_553_ = v_quotContext_586_;
v_currMacroScope_554_ = v_currMacroScope_587_;
v_cancelTk_x3f_555_ = v_cancelTk_x3f_588_;
v_inheritedTraceOptions_556_ = v_inheritedTraceOptions_589_;
v_currRecDepth_557_ = v_currRecDepth_575_;
v_ref_558_ = v_ref_576_;
v_suppressElabErrors_559_ = v_suppressElabErrors_577_;
v_isRecordingDeps_560_ = v_isRecordingDeps_578_;
v___y_561_ = v___y_462_;
goto v___jp_544_;
}
}
}
v___jp_615_:
{
uint16_t v___x_617_; lean_object* v___x_618_; lean_object* v_env_619_; uint8_t v___x_620_; uint16_t v___x_621_; uint16_t v___x_622_; uint16_t v___x_623_; uint8_t v___x_624_; 
v___x_617_ = l_Lean_OptionFlags_ofOptions(v___y_616_);
v___x_618_ = lean_st_ref_get(v___y_462_);
v_env_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_618_);
v___x_620_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_619_);
lean_dec_ref(v_env_619_);
v___x_621_ = 512;
v___x_622_ = lean_uint16_land(v___x_617_, v___x_621_);
v___x_623_ = 0;
v___x_624_ = lean_uint16_dec_eq(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
if (v___x_620_ == 0)
{
v___y_591_ = v___x_617_;
v___y_592_ = v___x_456_;
v___y_593_ = v___y_616_;
goto v___jp_590_;
}
else
{
v___y_545_ = v___x_617_;
v___y_546_ = v___y_616_;
v_fileName_547_ = v_fileName_579_;
v_fileMap_548_ = v_fileMap_580_;
v_currNamespace_549_ = v_currNamespace_582_;
v_openDecls_550_ = v_openDecls_583_;
v_initHeartbeats_551_ = v_initHeartbeats_584_;
v_maxHeartbeats_552_ = v_maxHeartbeats_585_;
v_quotContext_553_ = v_quotContext_586_;
v_currMacroScope_554_ = v_currMacroScope_587_;
v_cancelTk_x3f_555_ = v_cancelTk_x3f_588_;
v_inheritedTraceOptions_556_ = v_inheritedTraceOptions_589_;
v_currRecDepth_557_ = v_currRecDepth_575_;
v_ref_558_ = v_ref_576_;
v_suppressElabErrors_559_ = v_suppressElabErrors_577_;
v_isRecordingDeps_560_ = v_isRecordingDeps_578_;
v___y_561_ = v___y_462_;
goto v___jp_544_;
}
}
else
{
if (v___x_620_ == 0)
{
v___y_545_ = v___x_617_;
v___y_546_ = v___y_616_;
v_fileName_547_ = v_fileName_579_;
v_fileMap_548_ = v_fileMap_580_;
v_currNamespace_549_ = v_currNamespace_582_;
v_openDecls_550_ = v_openDecls_583_;
v_initHeartbeats_551_ = v_initHeartbeats_584_;
v_maxHeartbeats_552_ = v_maxHeartbeats_585_;
v_quotContext_553_ = v_quotContext_586_;
v_currMacroScope_554_ = v_currMacroScope_587_;
v_cancelTk_x3f_555_ = v_cancelTk_x3f_588_;
v_inheritedTraceOptions_556_ = v_inheritedTraceOptions_589_;
v_currRecDepth_557_ = v_currRecDepth_575_;
v_ref_558_ = v_ref_576_;
v_suppressElabErrors_559_ = v_suppressElabErrors_577_;
v_isRecordingDeps_560_ = v_isRecordingDeps_578_;
v___y_561_ = v___y_462_;
goto v___jp_544_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
v___y_591_ = v___x_617_;
v___y_592_ = v___x_625_;
v___y_593_ = v___y_616_;
goto v___jp_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v___x_631_, lean_object* v___f_632_, lean_object* v_declNames_633_, lean_object* v___x_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_7118__boxed_638_; lean_object* v_res_639_; 
v___x_7118__boxed_638_ = lean_unbox(v___x_630_);
v_res_639_ = l_Lean_Compiler_compile___lam__1(v___x_629_, v___x_7118__boxed_638_, v___x_631_, v___f_632_, v_declNames_633_, v___x_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc_ref(v_declNames_645_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_649_, 0, v_declNames_645_);
v___x_650_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_646_);
v___x_651_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_652_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_653_ = l_Lean_Options_empty;
v___x_654_ = 1;
v___x_655_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_656_ = lean_box(v___x_654_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_657_, 0, v___x_652_);
lean_closure_set(v___f_657_, 1, v___x_656_);
lean_closure_set(v___f_657_, 2, v___x_655_);
lean_closure_set(v___f_657_, 3, v___f_649_);
lean_closure_set(v___f_657_, 4, v_declNames_645_);
lean_closure_set(v___f_657_, 5, v___x_653_);
v___x_658_ = lean_box(0);
v___x_659_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_651_, v___x_650_, v___f_657_, v___x_658_, v_a_646_, v_a_647_);
lean_dec_ref(v___x_650_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Compiler_compile(v_declNames_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object* v_00_u03b1_665_, lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_666_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object* v_00_u03b1_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_00_u03b1_671_, v_x_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_737_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_738_ = 0;
v___x_739_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_740_ = l_Lean_registerTraceClass(v___x_737_, v___x_738_, v___x_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref_known(v___x_740_, 1);
v___x_741_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_742_ = l_Lean_registerTraceClass(v___x_741_, v___x_738_, v___x_739_);
return v___x_742_;
}
else
{
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_744_;
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

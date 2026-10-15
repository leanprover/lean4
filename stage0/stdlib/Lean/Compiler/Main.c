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
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_ctor_set(v___x_202_, 2, v___x_201_);
lean_ctor_set(v___x_202_, 3, v___x_201_);
lean_ctor_set(v___x_202_, 4, v___x_200_);
lean_ctor_set(v___x_202_, 5, v___x_200_);
lean_ctor_set(v___x_202_, 6, v___x_200_);
lean_ctor_set(v___x_202_, 7, v___x_200_);
lean_ctor_set(v___x_202_, 8, v___x_200_);
lean_ctor_set(v___x_202_, 9, v___x_200_);
lean_ctor_set(v___x_202_, 10, v___x_200_);
lean_ctor_set(v___x_202_, 11, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_unsigned_to_nat(32u);
v___x_204_ = lean_mk_empty_array_with_capacity(v___x_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4(void){
_start:
{
size_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_206_ = ((size_t)5ULL);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_unsigned_to_nat(32u);
v___x_209_ = lean_mk_empty_array_with_capacity(v___x_208_);
v___x_210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3);
v___x_211_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_207_);
lean_ctor_set(v___x_211_, 3, v___x_207_);
lean_ctor_set_usize(v___x_211_, 4, v___x_206_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_box(1);
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4);
v___x_214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_212_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(lean_object* v_msgData_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v_toCold_221_; lean_object* v_env_222_; lean_object* v_options_223_; uint8_t v___x_224_; lean_object* v_env_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_220_ = lean_st_ref_get(v___y_218_);
v_toCold_221_ = lean_ctor_get(v___y_217_, 0);
v_env_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref(v_env_222_);
lean_dec(v___x_220_);
v_options_223_ = lean_ctor_get(v_toCold_221_, 2);
v___x_224_ = 0;
v_env_225_ = l_Lean_Environment_setRecordingDeps(v_env_222_, v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2);
v___x_227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5);
lean_inc_ref(v_options_223_);
v___x_228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_228_, 0, v_env_225_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
lean_ctor_set(v___x_228_, 3, v_options_223_);
v___x_229_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_msgData_216_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___boxed(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msgData_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object* v_oldTraces_236_, lean_object* v_data_237_, lean_object* v_ref_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_toCold_243_; lean_object* v_currRecDepth_244_; lean_object* v_ref_245_; uint16_t v_optionFlags_246_; uint8_t v_suppressElabErrors_247_; uint8_t v_isRecordingDeps_248_; lean_object* v_ref_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_traceState_252_; lean_object* v_traces_253_; lean_object* v___x_254_; size_t v_sz_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v_msg_258_; lean_object* v___x_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_298_; 
v_toCold_243_ = lean_ctor_get(v___y_240_, 0);
v_currRecDepth_244_ = lean_ctor_get(v___y_240_, 1);
v_ref_245_ = lean_ctor_get(v___y_240_, 2);
v_optionFlags_246_ = lean_ctor_get_uint16(v___y_240_, sizeof(void*)*3);
v_suppressElabErrors_247_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*3 + 2);
v_isRecordingDeps_248_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*3 + 3);
v_ref_249_ = l_Lean_replaceRef(v_ref_238_, v_ref_245_);
lean_inc(v_currRecDepth_244_);
lean_inc_ref(v_toCold_243_);
v___x_250_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_250_, 0, v_toCold_243_);
lean_ctor_set(v___x_250_, 1, v_currRecDepth_244_);
lean_ctor_set(v___x_250_, 2, v_ref_249_);
lean_ctor_set_uint16(v___x_250_, sizeof(void*)*3, v_optionFlags_246_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*3 + 2, v_suppressElabErrors_247_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*3 + 3, v_isRecordingDeps_248_);
v___x_251_ = lean_st_ref_get(v___y_241_);
v_traceState_252_ = lean_ctor_get(v___x_251_, 4);
lean_inc_ref(v_traceState_252_);
lean_dec(v___x_251_);
v_traces_253_ = lean_ctor_get(v_traceState_252_, 0);
lean_inc_ref(v_traces_253_);
lean_dec_ref(v_traceState_252_);
v___x_254_ = l_Lean_PersistentArray_toArray___redArg(v_traces_253_);
lean_dec_ref(v_traces_253_);
v_sz_255_ = lean_array_size(v___x_254_);
v___x_256_ = ((size_t)0ULL);
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_255_, v___x_256_, v___x_254_);
v_msg_258_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_258_, 0, v_data_237_);
lean_ctor_set(v_msg_258_, 1, v_msg_239_);
lean_ctor_set(v_msg_258_, 2, v___x_257_);
v___x_259_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msg_258_, v___x_250_, v___y_241_);
lean_dec_ref_known(v___x_250_, 3);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_298_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_298_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_298_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v_traceState_265_; lean_object* v_env_266_; lean_object* v_nextMacroScope_267_; lean_object* v_ngen_268_; lean_object* v_auxDeclNGen_269_; lean_object* v_cache_270_; lean_object* v_recordedDeps_271_; lean_object* v_messages_272_; lean_object* v_infoState_273_; lean_object* v_snapshotTasks_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_297_; 
v___x_264_ = lean_st_ref_take(v___y_241_);
v_traceState_265_ = lean_ctor_get(v___x_264_, 4);
v_env_266_ = lean_ctor_get(v___x_264_, 0);
v_nextMacroScope_267_ = lean_ctor_get(v___x_264_, 1);
v_ngen_268_ = lean_ctor_get(v___x_264_, 2);
v_auxDeclNGen_269_ = lean_ctor_get(v___x_264_, 3);
v_cache_270_ = lean_ctor_get(v___x_264_, 5);
v_recordedDeps_271_ = lean_ctor_get(v___x_264_, 6);
v_messages_272_ = lean_ctor_get(v___x_264_, 7);
v_infoState_273_ = lean_ctor_get(v___x_264_, 8);
v_snapshotTasks_274_ = lean_ctor_get(v___x_264_, 9);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_297_ == 0)
{
v___x_276_ = v___x_264_;
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snapshotTasks_274_);
lean_inc(v_infoState_273_);
lean_inc(v_messages_272_);
lean_inc(v_recordedDeps_271_);
lean_inc(v_cache_270_);
lean_inc(v_traceState_265_);
lean_inc(v_auxDeclNGen_269_);
lean_inc(v_ngen_268_);
lean_inc(v_nextMacroScope_267_);
lean_inc(v_env_266_);
lean_dec(v___x_264_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint64_t v_tid_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_295_; 
v_tid_278_ = lean_ctor_get_uint64(v_traceState_265_, sizeof(void*)*1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_traceState_265_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_traceState_265_, 0);
lean_dec(v_unused_296_);
v___x_280_ = v_traceState_265_;
v_isShared_281_ = v_isSharedCheck_295_;
goto v_resetjp_279_;
}
else
{
lean_dec(v_traceState_265_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_295_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_ref_238_);
lean_ctor_set(v___x_283_, 1, v_a_260_);
v___x_284_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_236_, v___x_283_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_286_ = v___x_280_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_284_);
lean_ctor_set_uint64(v_reuseFailAlloc_294_, sizeof(void*)*1, v_tid_278_);
v___x_286_ = v_reuseFailAlloc_294_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 4, v___x_286_);
v___x_288_ = v___x_276_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_env_266_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_nextMacroScope_267_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_ngen_268_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_auxDeclNGen_269_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v_cache_270_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_recordedDeps_271_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_messages_272_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_infoState_273_);
lean_ctor_set(v_reuseFailAlloc_293_, 9, v_snapshotTasks_274_);
v___x_288_ = v_reuseFailAlloc_293_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_st_ref_put(v___y_241_, v___x_288_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_282_);
v___x_291_ = v___x_262_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_282_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object* v_oldTraces_299_, lean_object* v_data_300_, lean_object* v_ref_301_, lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_299_, v_data_300_, v_ref_301_, v_msg_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_306_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0(void){
_start:
{
lean_object* v___x_307_; double v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_float_of_nat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3(void){
_start:
{
lean_object* v___x_312_; double v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1000u);
v___x_313_ = lean_float_of_nat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_314_, uint8_t v_collapsed_315_, lean_object* v_tag_316_, lean_object* v_opts_317_, uint8_t v_clsEnabled_318_, lean_object* v_oldTraces_319_, lean_object* v_msg_320_, lean_object* v_resStartStop_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v_data_330_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___y_338_; lean_object* v_a_339_; uint8_t v___y_354_; double v___y_386_; 
v_fst_325_ = lean_ctor_get(v_resStartStop_321_, 0);
lean_inc(v_fst_325_);
v_snd_326_ = lean_ctor_get(v_resStartStop_321_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v_resStartStop_321_);
v_fst_333_ = lean_ctor_get(v_snd_326_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_snd_326_, 1);
lean_inc(v_snd_334_);
lean_dec(v_snd_326_);
v___x_335_ = l_Lean_trace_profiler;
v___x_336_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_317_, v___x_335_);
if (v___x_336_ == 0)
{
v___y_354_ = v___x_336_;
goto v___jp_353_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = l_Lean_trace_profiler_useHeartbeats;
v___x_392_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_317_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; double v___x_395_; double v___x_396_; double v___x_397_; 
v___x_393_ = l_Lean_trace_profiler_threshold;
v___x_394_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_317_, v___x_393_);
v___x_395_ = lean_float_of_nat(v___x_394_);
v___x_396_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3);
v___x_397_ = lean_float_div(v___x_395_, v___x_396_);
v___y_386_ = v___x_397_;
goto v___jp_385_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; double v___x_400_; 
v___x_398_ = l_Lean_trace_profiler_threshold;
v___x_399_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_317_, v___x_398_);
v___x_400_ = lean_float_of_nat(v___x_399_);
v___y_386_ = v___x_400_;
goto v___jp_385_;
}
}
v___jp_327_:
{
lean_object* v___x_331_; 
lean_inc(v___y_328_);
v___x_331_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_319_, v_data_330_, v___y_328_, v___y_329_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; 
lean_dec_ref_known(v___x_331_, 1);
v___x_332_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_325_);
return v___x_332_;
}
else
{
lean_dec(v_fst_325_);
return v___x_331_;
}
}
v___jp_337_:
{
uint8_t v_result_340_; lean_object* v___x_341_; lean_object* v___x_342_; double v___x_343_; lean_object* v_data_344_; 
v_result_340_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_fst_325_);
v___x_341_ = lean_box(v_result_340_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
v___x_343_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0);
lean_inc_ref(v_tag_316_);
lean_inc_ref(v___x_342_);
lean_inc(v_cls_314_);
v_data_344_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_344_, 0, v_cls_314_);
lean_ctor_set(v_data_344_, 1, v___x_342_);
lean_ctor_set(v_data_344_, 2, v_tag_316_);
lean_ctor_set_float(v_data_344_, sizeof(void*)*3, v___x_343_);
lean_ctor_set_float(v_data_344_, sizeof(void*)*3 + 8, v___x_343_);
lean_ctor_set_uint8(v_data_344_, sizeof(void*)*3 + 16, v_collapsed_315_);
if (v___x_336_ == 0)
{
lean_dec_ref_known(v___x_342_, 1);
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
lean_dec_ref(v_tag_316_);
lean_dec(v_cls_314_);
v___y_328_ = v___y_338_;
v___y_329_ = v_a_339_;
v_data_330_ = v_data_344_;
goto v___jp_327_;
}
else
{
lean_object* v_data_345_; double v___x_346_; double v___x_347_; 
lean_dec_ref_known(v_data_344_, 3);
v_data_345_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_345_, 0, v_cls_314_);
lean_ctor_set(v_data_345_, 1, v___x_342_);
lean_ctor_set(v_data_345_, 2, v_tag_316_);
v___x_346_ = lean_unbox_float(v_fst_333_);
lean_dec(v_fst_333_);
lean_ctor_set_float(v_data_345_, sizeof(void*)*3, v___x_346_);
v___x_347_ = lean_unbox_float(v_snd_334_);
lean_dec(v_snd_334_);
lean_ctor_set_float(v_data_345_, sizeof(void*)*3 + 8, v___x_347_);
lean_ctor_set_uint8(v_data_345_, sizeof(void*)*3 + 16, v_collapsed_315_);
v___y_328_ = v___y_338_;
v___y_329_ = v_a_339_;
v_data_330_ = v_data_345_;
goto v___jp_327_;
}
}
v___jp_348_:
{
lean_object* v_ref_349_; lean_object* v___x_350_; 
v_ref_349_ = lean_ctor_get(v___y_322_, 2);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v_fst_325_);
v___x_350_ = lean_apply_4(v_msg_320_, v_fst_325_, v___y_322_, v___y_323_, lean_box(0));
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___y_338_ = v_ref_349_;
v_a_339_ = v_a_351_;
goto v___jp_337_;
}
else
{
lean_object* v___x_352_; 
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2);
v___y_338_ = v_ref_349_;
v_a_339_ = v___x_352_;
goto v___jp_337_;
}
}
v___jp_353_:
{
if (v_clsEnabled_318_ == 0)
{
if (v___y_354_ == 0)
{
lean_object* v___x_355_; lean_object* v_traceState_356_; lean_object* v_env_357_; lean_object* v_nextMacroScope_358_; lean_object* v_ngen_359_; lean_object* v_auxDeclNGen_360_; lean_object* v_cache_361_; lean_object* v_recordedDeps_362_; lean_object* v_messages_363_; lean_object* v_infoState_364_; lean_object* v_snapshotTasks_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
lean_dec_ref(v_msg_320_);
lean_dec_ref(v_tag_316_);
lean_dec(v_cls_314_);
v___x_355_ = lean_st_ref_take(v___y_323_);
v_traceState_356_ = lean_ctor_get(v___x_355_, 4);
v_env_357_ = lean_ctor_get(v___x_355_, 0);
v_nextMacroScope_358_ = lean_ctor_get(v___x_355_, 1);
v_ngen_359_ = lean_ctor_get(v___x_355_, 2);
v_auxDeclNGen_360_ = lean_ctor_get(v___x_355_, 3);
v_cache_361_ = lean_ctor_get(v___x_355_, 5);
v_recordedDeps_362_ = lean_ctor_get(v___x_355_, 6);
v_messages_363_ = lean_ctor_get(v___x_355_, 7);
v_infoState_364_ = lean_ctor_get(v___x_355_, 8);
v_snapshotTasks_365_ = lean_ctor_get(v___x_355_, 9);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_384_ == 0)
{
v___x_367_ = v___x_355_;
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snapshotTasks_365_);
lean_inc(v_infoState_364_);
lean_inc(v_messages_363_);
lean_inc(v_recordedDeps_362_);
lean_inc(v_cache_361_);
lean_inc(v_traceState_356_);
lean_inc(v_auxDeclNGen_360_);
lean_inc(v_ngen_359_);
lean_inc(v_nextMacroScope_358_);
lean_inc(v_env_357_);
lean_dec(v___x_355_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint64_t v_tid_369_; lean_object* v_traces_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_383_; 
v_tid_369_ = lean_ctor_get_uint64(v_traceState_356_, sizeof(void*)*1);
v_traces_370_ = lean_ctor_get(v_traceState_356_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_traceState_356_);
if (v_isSharedCheck_383_ == 0)
{
v___x_372_ = v_traceState_356_;
v_isShared_373_ = v_isSharedCheck_383_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_traces_370_);
lean_dec(v_traceState_356_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_383_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_319_, v_traces_370_);
lean_dec_ref(v_traces_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_374_);
lean_ctor_set_uint64(v_reuseFailAlloc_382_, sizeof(void*)*1, v_tid_369_);
v___x_376_ = v_reuseFailAlloc_382_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v___x_376_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_env_357_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_nextMacroScope_358_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_ngen_359_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_auxDeclNGen_360_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_cache_361_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_recordedDeps_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_messages_363_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v_infoState_364_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v_snapshotTasks_365_);
v___x_378_ = v_reuseFailAlloc_381_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_st_ref_put(v___y_323_, v___x_378_);
v___x_380_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_325_);
return v___x_380_;
}
}
}
}
}
else
{
goto v___jp_348_;
}
}
else
{
goto v___jp_348_;
}
}
v___jp_385_:
{
double v___x_387_; double v___x_388_; double v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unbox_float(v_snd_334_);
v___x_388_ = lean_unbox_float(v_fst_333_);
v___x_389_ = lean_float_sub(v___x_387_, v___x_388_);
v___x_390_ = lean_float_decLt(v___y_386_, v___x_389_);
v___y_354_ = v___x_390_;
goto v___jp_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_401_, lean_object* v_collapsed_402_, lean_object* v_tag_403_, lean_object* v_opts_404_, lean_object* v_clsEnabled_405_, lean_object* v_oldTraces_406_, lean_object* v_msg_407_, lean_object* v_resStartStop_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_collapsed_boxed_412_; uint8_t v_clsEnabled_boxed_413_; lean_object* v_res_414_; 
v_collapsed_boxed_412_ = lean_unbox(v_collapsed_402_);
v_clsEnabled_boxed_413_ = lean_unbox(v_clsEnabled_405_);
v_res_414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_401_, v_collapsed_boxed_412_, v_tag_403_, v_opts_404_, v_clsEnabled_boxed_413_, v_oldTraces_406_, v_msg_407_, v_resStartStop_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec_ref(v_opts_404_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_o_418_, lean_object* v_k_419_, uint8_t v_v_420_){
_start:
{
lean_object* v_map_421_; uint8_t v_hasTrace_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_436_; 
v_map_421_ = lean_ctor_get(v_o_418_, 0);
v_hasTrace_422_ = lean_ctor_get_uint8(v_o_418_, sizeof(void*)*1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_o_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_424_ = v_o_418_;
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_map_421_);
lean_dec(v_o_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_426_, 0, v_v_420_);
lean_inc(v_k_419_);
v___x_427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_419_, v___x_426_, v_map_421_);
if (v_hasTrace_422_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_431_; 
v___x_428_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
v___x_429_ = l_Lean_Name_isPrefixOf(v___x_428_, v_k_419_);
lean_dec(v_k_419_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_427_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*1, v___x_429_);
return v___x_431_;
}
}
else
{
lean_object* v___x_434_; 
lean_dec(v_k_419_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_434_ = v___x_424_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*1, v_hasTrace_422_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_o_437_, lean_object* v_k_438_, lean_object* v_v_439_){
_start:
{
uint8_t v_v_boxed_440_; lean_object* v_res_441_; 
v_v_boxed_440_ = lean_unbox(v_v_439_);
v_res_441_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_o_437_, v_k_438_, v_v_boxed_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(lean_object* v_opts_442_, lean_object* v_opt_443_, uint8_t v_val_444_){
_start:
{
lean_object* v_name_445_; lean_object* v___x_446_; 
v_name_445_ = lean_ctor_get(v_opt_443_, 0);
lean_inc(v_name_445_);
lean_dec_ref(v_opt_443_);
v___x_446_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_opts_442_, v_name_445_, v_val_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_opts_447_, lean_object* v_opt_448_, lean_object* v_val_449_){
_start:
{
uint8_t v_val_boxed_450_; lean_object* v_res_451_; 
v_val_boxed_450_ = lean_unbox(v_val_449_);
v_res_451_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_opts_447_, v_opt_448_, v_val_boxed_450_);
return v_res_451_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_452_; double v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(1000000000u);
v___x_453_ = lean_float_of_nat(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_458_, uint8_t v___x_459_, lean_object* v___x_460_, lean_object* v___f_461_, lean_object* v_declNames_462_, lean_object* v___x_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v_a_474_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; lean_object* v_a_490_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; lean_object* v___y_548_; uint16_t v___y_549_; lean_object* v_fileName_550_; lean_object* v_fileMap_551_; lean_object* v_currNamespace_552_; lean_object* v_openDecls_553_; lean_object* v_initHeartbeats_554_; lean_object* v_maxHeartbeats_555_; lean_object* v_quotContext_556_; lean_object* v_currMacroScope_557_; lean_object* v_cancelTk_x3f_558_; lean_object* v_inheritedTraceOptions_559_; lean_object* v_currRecDepth_560_; lean_object* v_ref_561_; uint8_t v_suppressElabErrors_562_; uint8_t v_isRecordingDeps_563_; lean_object* v___y_564_; lean_object* v_toCold_577_; lean_object* v_currRecDepth_578_; lean_object* v_ref_579_; uint8_t v_suppressElabErrors_580_; uint8_t v_isRecordingDeps_581_; lean_object* v_fileName_582_; lean_object* v_fileMap_583_; lean_object* v_options_584_; lean_object* v_currNamespace_585_; lean_object* v_openDecls_586_; lean_object* v_initHeartbeats_587_; lean_object* v_maxHeartbeats_588_; lean_object* v_quotContext_589_; lean_object* v_currMacroScope_590_; lean_object* v_cancelTk_x3f_591_; lean_object* v_inheritedTraceOptions_592_; lean_object* v___y_594_; uint8_t v___y_595_; uint16_t v___y_596_; lean_object* v___y_619_; 
v_toCold_577_ = lean_ctor_get(v___y_464_, 0);
lean_inc_ref(v_toCold_577_);
v_currRecDepth_578_ = lean_ctor_get(v___y_464_, 1);
lean_inc(v_currRecDepth_578_);
v_ref_579_ = lean_ctor_get(v___y_464_, 2);
lean_inc(v_ref_579_);
v_suppressElabErrors_580_ = lean_ctor_get_uint8(v___y_464_, sizeof(void*)*3 + 2);
v_isRecordingDeps_581_ = lean_ctor_get_uint8(v___y_464_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_464_);
v_fileName_582_ = lean_ctor_get(v_toCold_577_, 0);
lean_inc_ref(v_fileName_582_);
v_fileMap_583_ = lean_ctor_get(v_toCold_577_, 1);
lean_inc_ref(v_fileMap_583_);
v_options_584_ = lean_ctor_get(v_toCold_577_, 2);
lean_inc_ref(v_options_584_);
v_currNamespace_585_ = lean_ctor_get(v_toCold_577_, 4);
lean_inc(v_currNamespace_585_);
v_openDecls_586_ = lean_ctor_get(v_toCold_577_, 5);
lean_inc(v_openDecls_586_);
v_initHeartbeats_587_ = lean_ctor_get(v_toCold_577_, 6);
lean_inc(v_initHeartbeats_587_);
v_maxHeartbeats_588_ = lean_ctor_get(v_toCold_577_, 7);
lean_inc(v_maxHeartbeats_588_);
v_quotContext_589_ = lean_ctor_get(v_toCold_577_, 8);
lean_inc(v_quotContext_589_);
v_currMacroScope_590_ = lean_ctor_get(v_toCold_577_, 9);
lean_inc(v_currMacroScope_590_);
v_cancelTk_x3f_591_ = lean_ctor_get(v_toCold_577_, 10);
lean_inc(v_cancelTk_x3f_591_);
v_inheritedTraceOptions_592_ = lean_ctor_get(v_toCold_577_, 11);
lean_inc_ref(v_inheritedTraceOptions_592_);
lean_dec_ref(v_toCold_577_);
if (v_isRecordingDeps_581_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_630_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_options_584_, v___x_629_, v_isRecordingDeps_581_);
v___y_619_ = v___x_630_;
goto v___jp_618_;
}
else
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_584_);
v___y_619_ = v___x_631_;
goto v___jp_618_;
}
v___jp_467_:
{
lean_object* v___x_475_; double v___x_476_; double v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_475_ = lean_io_get_num_heartbeats();
v___x_476_ = lean_float_of_nat(v___y_472_);
v___x_477_ = lean_float_of_nat(v___x_475_);
v___x_478_ = lean_box_float(v___x_476_);
v___x_479_ = lean_box_float(v___x_477_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_a_474_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_458_, v___x_459_, v___x_460_, v___y_470_, v___y_473_, v___y_471_, v___f_461_, v___x_481_, v___y_468_, v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v___y_470_);
return v___x_482_;
}
v___jp_483_:
{
lean_object* v___x_491_; double v___x_492_; double v___x_493_; double v___x_494_; double v___x_495_; double v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_491_ = lean_io_mono_nanos_now();
v___x_492_ = lean_float_of_nat(v___y_485_);
v___x_493_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_494_ = lean_float_div(v___x_492_, v___x_493_);
v___x_495_ = lean_float_of_nat(v___x_491_);
v___x_496_ = lean_float_div(v___x_495_, v___x_493_);
v___x_497_ = lean_box_float(v___x_494_);
v___x_498_ = lean_box_float(v___x_496_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_a_490_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_458_, v___x_459_, v___x_460_, v___y_487_, v___y_489_, v___y_488_, v___f_461_, v___x_500_, v___y_484_, v___y_486_);
lean_dec_ref(v___y_484_);
lean_dec_ref(v___y_487_);
return v___x_501_;
}
v___jp_502_:
{
lean_object* v___x_507_; lean_object* v_a_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_504_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_trace_profiler_useHeartbeats;
v___x_510_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_505_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_io_mono_nanos_now();
v___x_512_ = l_Lean_Compiler_LCNF_main(v_declNames_462_, v___x_463_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v___y_484_ = v___y_503_;
v___y_485_ = v___x_511_;
v___y_486_ = v___y_504_;
v___y_487_ = v___y_505_;
v___y_488_ = v_a_508_;
v___y_489_ = v___y_506_;
v_a_490_ = v___x_518_;
goto v___jp_483_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_a_521_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_512_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 0);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_484_ = v___y_503_;
v___y_485_ = v___x_511_;
v___y_486_ = v___y_504_;
v___y_487_ = v___y_505_;
v___y_488_ = v_a_508_;
v___y_489_ = v___y_506_;
v_a_490_ = v___x_526_;
goto v___jp_483_;
}
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_io_get_num_heartbeats();
v___x_530_ = l_Lean_Compiler_LCNF_main(v_declNames_462_, v___x_463_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 1);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___y_505_;
v___y_471_ = v_a_508_;
v___y_472_ = v___x_529_;
v___y_473_ = v___y_506_;
v_a_474_ = v___x_536_;
goto v___jp_467_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_a_539_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___y_505_;
v___y_471_ = v_a_508_;
v___y_472_ = v___x_529_;
v___y_473_ = v___y_506_;
v_a_474_ = v___x_544_;
goto v___jp_467_;
}
}
}
}
}
v___jp_547_:
{
uint8_t v_hasTrace_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_hasTrace_565_ = lean_ctor_get_uint8(v___y_548_, sizeof(void*)*1);
v___x_566_ = l_Lean_maxRecDepth;
v___x_567_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v___y_548_, v___x_566_);
lean_inc_ref(v_inheritedTraceOptions_559_);
lean_inc_ref(v___y_548_);
v___x_568_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_568_, 0, v_fileName_550_);
lean_ctor_set(v___x_568_, 1, v_fileMap_551_);
lean_ctor_set(v___x_568_, 2, v___y_548_);
lean_ctor_set(v___x_568_, 3, v___x_567_);
lean_ctor_set(v___x_568_, 4, v_currNamespace_552_);
lean_ctor_set(v___x_568_, 5, v_openDecls_553_);
lean_ctor_set(v___x_568_, 6, v_initHeartbeats_554_);
lean_ctor_set(v___x_568_, 7, v_maxHeartbeats_555_);
lean_ctor_set(v___x_568_, 8, v_quotContext_556_);
lean_ctor_set(v___x_568_, 9, v_currMacroScope_557_);
lean_ctor_set(v___x_568_, 10, v_cancelTk_x3f_558_);
lean_ctor_set(v___x_568_, 11, v_inheritedTraceOptions_559_);
v___x_569_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_currRecDepth_560_);
lean_ctor_set(v___x_569_, 2, v_ref_561_);
lean_ctor_set_uint16(v___x_569_, sizeof(void*)*3, v___y_549_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3 + 2, v_suppressElabErrors_562_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3 + 3, v_isRecordingDeps_563_);
if (v_hasTrace_565_ == 0)
{
lean_object* v___x_570_; 
lean_dec_ref(v_inheritedTraceOptions_559_);
lean_dec_ref(v___y_548_);
lean_dec_ref(v___f_461_);
lean_dec_ref(v___x_460_);
lean_dec(v___x_458_);
v___x_570_ = l_Lean_Compiler_LCNF_main(v_declNames_462_, v___x_463_, v___x_569_, v___y_564_);
lean_dec_ref_known(v___x_569_, 3);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
lean_inc(v___x_458_);
v___x_572_ = l_Lean_Name_append(v___x_571_, v___x_458_);
v___x_573_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_559_, v___y_548_, v___x_572_);
lean_dec(v___x_572_);
lean_dec_ref(v_inheritedTraceOptions_559_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = l_Lean_trace_profiler;
v___x_575_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_548_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v___y_548_);
lean_dec_ref(v___f_461_);
lean_dec_ref(v___x_460_);
lean_dec(v___x_458_);
v___x_576_ = l_Lean_Compiler_LCNF_main(v_declNames_462_, v___x_463_, v___x_569_, v___y_564_);
lean_dec_ref_known(v___x_569_, 3);
return v___x_576_;
}
else
{
v___y_503_ = v___x_569_;
v___y_504_ = v___y_564_;
v___y_505_ = v___y_548_;
v___y_506_ = v___x_573_;
goto v___jp_502_;
}
}
else
{
v___y_503_ = v___x_569_;
v___y_504_ = v___y_564_;
v___y_505_ = v___y_548_;
v___y_506_ = v___x_573_;
goto v___jp_502_;
}
}
}
v___jp_593_:
{
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v_nextMacroScope_599_; lean_object* v_ngen_600_; lean_object* v_auxDeclNGen_601_; lean_object* v_traceState_602_; lean_object* v_recordedDeps_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v___x_597_ = lean_st_ref_take(v___y_465_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
v_nextMacroScope_599_ = lean_ctor_get(v___x_597_, 1);
v_ngen_600_ = lean_ctor_get(v___x_597_, 2);
v_auxDeclNGen_601_ = lean_ctor_get(v___x_597_, 3);
v_traceState_602_ = lean_ctor_get(v___x_597_, 4);
v_recordedDeps_603_ = lean_ctor_get(v___x_597_, 6);
v_messages_604_ = lean_ctor_get(v___x_597_, 7);
v_infoState_605_ = lean_ctor_get(v___x_597_, 8);
v_snapshotTasks_606_ = lean_ctor_get(v___x_597_, 9);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_597_, 5);
lean_dec(v_unused_617_);
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_recordedDeps_603_);
lean_inc(v_traceState_602_);
lean_inc(v_auxDeclNGen_601_);
lean_inc(v_ngen_600_);
lean_inc(v_nextMacroScope_599_);
lean_inc(v_env_598_);
lean_dec(v___x_597_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = l_Lean_Kernel_enableDiag(v_env_598_, v___y_595_);
v___x_611_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 5, v___x_611_);
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_nextMacroScope_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_ngen_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_auxDeclNGen_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_traceState_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_recordedDeps_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 9, v_snapshotTasks_606_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_st_ref_put(v___y_465_, v___x_613_);
v___y_548_ = v___y_594_;
v___y_549_ = v___y_596_;
v_fileName_550_ = v_fileName_582_;
v_fileMap_551_ = v_fileMap_583_;
v_currNamespace_552_ = v_currNamespace_585_;
v_openDecls_553_ = v_openDecls_586_;
v_initHeartbeats_554_ = v_initHeartbeats_587_;
v_maxHeartbeats_555_ = v_maxHeartbeats_588_;
v_quotContext_556_ = v_quotContext_589_;
v_currMacroScope_557_ = v_currMacroScope_590_;
v_cancelTk_x3f_558_ = v_cancelTk_x3f_591_;
v_inheritedTraceOptions_559_ = v_inheritedTraceOptions_592_;
v_currRecDepth_560_ = v_currRecDepth_578_;
v_ref_561_ = v_ref_579_;
v_suppressElabErrors_562_ = v_suppressElabErrors_580_;
v_isRecordingDeps_563_ = v_isRecordingDeps_581_;
v___y_564_ = v___y_465_;
goto v___jp_547_;
}
}
}
v___jp_618_:
{
uint16_t v___x_620_; lean_object* v___x_621_; lean_object* v_env_622_; uint8_t v___x_623_; uint16_t v___x_624_; uint16_t v___x_625_; uint16_t v___x_626_; uint8_t v___x_627_; 
v___x_620_ = l_Lean_OptionFlags_ofOptions(v___y_619_);
v___x_621_ = lean_st_ref_get(v___y_465_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_622_);
lean_dec_ref(v_env_622_);
v___x_624_ = 512;
v___x_625_ = lean_uint16_land(v___x_620_, v___x_624_);
v___x_626_ = 0;
v___x_627_ = lean_uint16_dec_eq(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
if (v___x_623_ == 0)
{
v___y_594_ = v___y_619_;
v___y_595_ = v___x_459_;
v___y_596_ = v___x_620_;
goto v___jp_593_;
}
else
{
v___y_548_ = v___y_619_;
v___y_549_ = v___x_620_;
v_fileName_550_ = v_fileName_582_;
v_fileMap_551_ = v_fileMap_583_;
v_currNamespace_552_ = v_currNamespace_585_;
v_openDecls_553_ = v_openDecls_586_;
v_initHeartbeats_554_ = v_initHeartbeats_587_;
v_maxHeartbeats_555_ = v_maxHeartbeats_588_;
v_quotContext_556_ = v_quotContext_589_;
v_currMacroScope_557_ = v_currMacroScope_590_;
v_cancelTk_x3f_558_ = v_cancelTk_x3f_591_;
v_inheritedTraceOptions_559_ = v_inheritedTraceOptions_592_;
v_currRecDepth_560_ = v_currRecDepth_578_;
v_ref_561_ = v_ref_579_;
v_suppressElabErrors_562_ = v_suppressElabErrors_580_;
v_isRecordingDeps_563_ = v_isRecordingDeps_581_;
v___y_564_ = v___y_465_;
goto v___jp_547_;
}
}
else
{
if (v___x_623_ == 0)
{
v___y_548_ = v___y_619_;
v___y_549_ = v___x_620_;
v_fileName_550_ = v_fileName_582_;
v_fileMap_551_ = v_fileMap_583_;
v_currNamespace_552_ = v_currNamespace_585_;
v_openDecls_553_ = v_openDecls_586_;
v_initHeartbeats_554_ = v_initHeartbeats_587_;
v_maxHeartbeats_555_ = v_maxHeartbeats_588_;
v_quotContext_556_ = v_quotContext_589_;
v_currMacroScope_557_ = v_currMacroScope_590_;
v_cancelTk_x3f_558_ = v_cancelTk_x3f_591_;
v_inheritedTraceOptions_559_ = v_inheritedTraceOptions_592_;
v_currRecDepth_560_ = v_currRecDepth_578_;
v_ref_561_ = v_ref_579_;
v_suppressElabErrors_562_ = v_suppressElabErrors_580_;
v_isRecordingDeps_563_ = v_isRecordingDeps_581_;
v___y_564_ = v___y_465_;
goto v___jp_547_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
v___y_594_ = v___y_619_;
v___y_595_ = v___x_628_;
v___y_596_ = v___x_620_;
goto v___jp_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___f_635_, lean_object* v_declNames_636_, lean_object* v___x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_7135__boxed_641_; lean_object* v_res_642_; 
v___x_7135__boxed_641_ = lean_unbox(v___x_633_);
v_res_642_ = l_Lean_Compiler_compile___lam__1(v___x_632_, v___x_7135__boxed_641_, v___x_634_, v___f_635_, v_declNames_636_, v___x_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_inc_ref(v_declNames_648_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_652_, 0, v_declNames_648_);
v___x_653_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_649_);
v___x_654_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_655_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_656_ = l_Lean_Options_empty;
v___x_657_ = 1;
v___x_658_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_659_ = lean_box(v___x_657_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_660_, 0, v___x_655_);
lean_closure_set(v___f_660_, 1, v___x_659_);
lean_closure_set(v___f_660_, 2, v___x_658_);
lean_closure_set(v___f_660_, 3, v___f_652_);
lean_closure_set(v___f_660_, 4, v_declNames_648_);
lean_closure_set(v___f_660_, 5, v___x_656_);
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_654_, v___x_653_, v___f_660_, v___x_661_, v_a_649_, v_a_650_);
lean_dec_ref(v___x_653_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Compiler_compile(v_declNames_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_00_u03b1_674_, v_x_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_741_ = 0;
v___x_742_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_743_ = l_Lean_registerTraceClass(v___x_740_, v___x_741_, v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref_known(v___x_743_, 1);
v___x_744_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_745_ = l_Lean_registerTraceClass(v___x_744_, v___x_741_, v___x_742_);
return v___x_745_;
}
else
{
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_747_;
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

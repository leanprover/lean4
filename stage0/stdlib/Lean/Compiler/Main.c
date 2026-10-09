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
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(lean_object* v___y_21_){
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
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_21_ = stack[0].m_obj;
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_21_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg___boxed(lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_57_);
lean_dec(v___y_57_);
return v_res_59_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_60_ = stack[0].m_obj;
lean_object* v___y_61_ = stack[1].m_obj;
lean_object* v_res_64_;
v_res_64_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(v___y_60_, v___y_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___boxed(lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2(v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_68_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(lean_object* v_opts_69_, lean_object* v_opt_70_){
_start:
{
lean_object* v_name_71_; lean_object* v_defValue_72_; lean_object* v_map_73_; lean_object* v___x_74_; 
v_name_71_ = lean_ctor_get(v_opt_70_, 0);
v_defValue_72_ = lean_ctor_get(v_opt_70_, 1);
v_map_73_ = lean_ctor_get(v_opts_69_, 0);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_73_, v_name_71_);
if (lean_obj_tag(v___x_74_) == 0)
{
uint8_t v___x_75_; 
v___x_75_ = lean_unbox(v_defValue_72_);
return v___x_75_;
}
else
{
lean_object* v_val_76_; 
v_val_76_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_val_76_);
lean_dec_ref_known(v___x_74_, 1);
if (lean_obj_tag(v_val_76_) == 1)
{
uint8_t v_v_77_; 
v_v_77_ = lean_ctor_get_uint8(v_val_76_, 0);
lean_dec_ref_known(v_val_76_, 0);
return v_v_77_;
}
else
{
uint8_t v___x_78_; 
lean_dec(v_val_76_);
v___x_78_ = lean_unbox(v_defValue_72_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_69_ = stack[0].m_obj;
lean_object* v_opt_70_ = stack[1].m_obj;
uint8_t v_res_79_;
v_res_79_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_69_, v_opt_70_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(lean_object* v_opts_80_, lean_object* v_opt_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_80_, v_opt_81_);
lean_dec_ref(v_opt_81_);
lean_dec_ref(v_opts_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(lean_object* v_category_84_, lean_object* v_opts_85_, lean_object* v_act_86_, lean_object* v_decl_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
v___x_91_ = lean_apply_2(v_act_86_, v___y_88_, v___y_89_);
v___x_92_ = l_Lean_profileitIOUnsafe___redArg(v_category_84_, v_opts_85_, v___x_91_, v_decl_87_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_84_ = stack[0].m_obj;
lean_object* v_opts_85_ = stack[1].m_obj;
lean_object* v_act_86_ = stack[2].m_obj;
lean_object* v_decl_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_84_, v_opts_85_, v_act_86_, v_decl_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg___boxed(lean_object* v_category_94_, lean_object* v_opts_95_, lean_object* v_act_96_, lean_object* v_decl_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_94_, v_opts_95_, v_act_96_, v_decl_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec_ref(v_opts_95_);
lean_dec_ref(v_category_94_);
return v_res_101_;
}
}
lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(lean_object* v_00_u03b1_102_, lean_object* v_category_103_, lean_object* v_opts_104_, lean_object* v_act_105_, lean_object* v_decl_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v_category_103_, v_opts_104_, v_act_105_, v_decl_106_, v___y_107_, v___y_108_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_103_ = stack[1].m_obj;
lean_object* v_opts_104_ = stack[2].m_obj;
lean_object* v_act_105_ = stack[3].m_obj;
lean_object* v_decl_106_ = stack[4].m_obj;
lean_object* v___y_107_ = stack[5].m_obj;
lean_object* v___y_108_ = stack[6].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(lean_box(0), v_category_103_, v_opts_104_, v_act_105_, v_decl_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___boxed(lean_object* v_00_u03b1_112_, lean_object* v_category_113_, lean_object* v_opts_114_, lean_object* v_act_115_, lean_object* v_decl_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(v_00_u03b1_112_, v_category_113_, v_opts_114_, v_act_115_, v_decl_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v_opts_114_);
lean_dec_ref(v_category_113_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
if (lean_obj_tag(v_a_121_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = l_List_reverse___redArg(v_a_122_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_134_; 
v_head_124_ = lean_ctor_get(v_a_121_, 0);
v_tail_125_ = lean_ctor_get(v_a_121_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_a_121_);
if (v_isSharedCheck_134_ == 0)
{
v___x_127_ = v_a_121_;
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_tail_125_);
lean_inc(v_head_124_);
lean_dec(v_a_121_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = l_Lean_MessageData_ofName(v_head_124_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_a_122_);
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_a_122_);
v___x_131_ = v_reuseFailAlloc_133_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v_a_121_ = v_tail_125_;
v_a_122_ = v___x_131_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Compiler_compile___lam__0___closed__0));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
lean_object* l_Lean_Compiler_compile___lam__0(lean_object* v_declNames_138_, lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_143_ = lean_obj_once(&l_Lean_Compiler_compile___lam__0___closed__1, &l_Lean_Compiler_compile___lam__0___closed__1_once, _init_l_Lean_Compiler_compile___lam__0___closed__1);
v___x_144_ = lean_array_to_list(v_declNames_138_);
v___x_145_ = lean_box(0);
v___x_146_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_144_, v___x_145_);
v___x_147_ = l_Lean_MessageData_ofList(v___x_146_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_143_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l_Lean_Compiler_compile___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_138_ = stack[0].m_obj;
lean_object* v_x_139_ = stack[1].m_obj;
lean_object* v___y_140_ = stack[2].m_obj;
lean_object* v___y_141_ = stack[3].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_Compiler_compile___lam__0(v_declNames_138_, v_x_139_, v___y_140_, v___y_141_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* v_declNames_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_compile___lam__0(v_declNames_151_, v_x_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec_ref(v_x_152_);
return v_res_156_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(lean_object* v_e_157_){
_start:
{
if (lean_obj_tag(v_e_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 2;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_157_ = stack[0].m_obj;
uint8_t v_res_160_;
v_res_160_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_e_157_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6___boxed(lean_object* v_e_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_e_161_);
lean_dec_ref(v_e_161_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v_x_164_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v_x_164_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v_x_164_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 1);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_a_174_ = lean_ctor_get(v_x_164_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v_x_164_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v_x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_164_ = stack[0].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_164_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg___boxed(lean_object* v_x_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_183_);
return v_res_185_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(size_t v_sz_186_, size_t v_i_187_, lean_object* v_bs_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_lt(v_i_187_, v_sz_186_);
if (v___x_189_ == 0)
{
return v_bs_188_;
}
else
{
lean_object* v_v_190_; lean_object* v_msg_191_; lean_object* v___x_192_; lean_object* v_bs_x27_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v_v_190_ = lean_array_uget_borrowed(v_bs_188_, v_i_187_);
v_msg_191_ = lean_ctor_get(v_v_190_, 1);
lean_inc_ref(v_msg_191_);
v___x_192_ = lean_unsigned_to_nat(0u);
v_bs_x27_193_ = lean_array_uset(v_bs_188_, v_i_187_, v___x_192_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_187_, v___x_194_);
v___x_196_ = lean_array_uset(v_bs_x27_193_, v_i_187_, v_msg_191_);
v_i_187_ = v___x_195_;
v_bs_188_ = v___x_196_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_186_ = stack[0].m_num;
size_t v_i_187_ = stack[1].m_num;
lean_object* v_bs_188_ = stack[2].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_186_, v_i_187_, v_bs_188_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6___boxed(lean_object* v_sz_199_, lean_object* v_i_200_, lean_object* v_bs_201_){
_start:
{
size_t v_sz_boxed_202_; size_t v_i_boxed_203_; lean_object* v_res_204_; 
v_sz_boxed_202_ = lean_unbox_usize(v_sz_199_);
lean_dec(v_sz_199_);
v_i_boxed_203_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_boxed_202_, v_i_boxed_203_, v_bs_201_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___x_210_);
lean_ctor_set(v___x_211_, 3, v___x_210_);
lean_ctor_set(v___x_211_, 4, v___x_209_);
lean_ctor_set(v___x_211_, 5, v___x_209_);
lean_ctor_set(v___x_211_, 6, v___x_209_);
lean_ctor_set(v___x_211_, 7, v___x_209_);
lean_ctor_set(v___x_211_, 8, v___x_209_);
lean_ctor_set(v___x_211_, 9, v___x_209_);
lean_ctor_set(v___x_211_, 10, v___x_209_);
lean_ctor_set(v___x_211_, 11, v___x_208_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(32u);
v___x_213_ = lean_mk_empty_array_with_capacity(v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4(void){
_start:
{
size_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = ((size_t)5ULL);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_unsigned_to_nat(32u);
v___x_218_ = lean_mk_empty_array_with_capacity(v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__3);
v___x_220_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_216_);
lean_ctor_set(v___x_220_, 3, v___x_216_);
lean_ctor_set_usize(v___x_220_, 4, v___x_215_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_box(1);
v___x_222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__4);
v___x_223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__1);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_221_);
return v___x_224_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_toCold_230_; lean_object* v_env_231_; lean_object* v_options_232_; uint8_t v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_229_ = lean_st_ref_get(v___y_227_);
v_toCold_230_ = lean_ctor_get(v___y_226_, 0);
v_env_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_env_231_);
lean_dec(v___x_229_);
v_options_232_ = lean_ctor_get(v_toCold_230_, 2);
v___x_233_ = 0;
v_env_234_ = l_Lean_Environment_setRecordingDeps(v_env_231_, v___x_233_);
v___x_235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__2);
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__5);
lean_inc_ref(v_options_232_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_234_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_ctor_set(v___x_237_, 3, v_options_232_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_225_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_225_ = stack[0].m_obj;
lean_object* v___y_226_ = stack[1].m_obj;
lean_object* v___y_227_ = stack[2].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msgData_225_, v___y_226_, v___y_227_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___boxed(lean_object* v_msgData_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msgData_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_245_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(lean_object* v_oldTraces_246_, lean_object* v_data_247_, lean_object* v_ref_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_toCold_253_; lean_object* v_currRecDepth_254_; lean_object* v_ref_255_; uint16_t v_optionFlags_256_; uint8_t v_suppressElabErrors_257_; uint8_t v_isRecordingDeps_258_; lean_object* v_ref_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_traceState_262_; lean_object* v_traces_263_; lean_object* v___x_264_; size_t v_sz_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v_msg_268_; lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_308_; 
v_toCold_253_ = lean_ctor_get(v___y_250_, 0);
v_currRecDepth_254_ = lean_ctor_get(v___y_250_, 1);
v_ref_255_ = lean_ctor_get(v___y_250_, 2);
v_optionFlags_256_ = lean_ctor_get_uint16(v___y_250_, sizeof(void*)*3);
v_suppressElabErrors_257_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*3 + 2);
v_isRecordingDeps_258_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*3 + 3);
v_ref_259_ = l_Lean_replaceRef(v_ref_248_, v_ref_255_);
lean_inc(v_currRecDepth_254_);
lean_inc_ref(v_toCold_253_);
v___x_260_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_260_, 0, v_toCold_253_);
lean_ctor_set(v___x_260_, 1, v_currRecDepth_254_);
lean_ctor_set(v___x_260_, 2, v_ref_259_);
lean_ctor_set_uint16(v___x_260_, sizeof(void*)*3, v_optionFlags_256_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*3 + 2, v_suppressElabErrors_257_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*3 + 3, v_isRecordingDeps_258_);
v___x_261_ = lean_st_ref_get(v___y_251_);
v_traceState_262_ = lean_ctor_get(v___x_261_, 4);
lean_inc_ref(v_traceState_262_);
lean_dec(v___x_261_);
v_traces_263_ = lean_ctor_get(v_traceState_262_, 0);
lean_inc_ref(v_traces_263_);
lean_dec_ref(v_traceState_262_);
v___x_264_ = l_Lean_PersistentArray_toArray___redArg(v_traces_263_);
lean_dec_ref(v_traces_263_);
v_sz_265_ = lean_array_size(v___x_264_);
v___x_266_ = ((size_t)0ULL);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_265_, v___x_266_, v___x_264_);
v_msg_268_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_268_, 0, v_data_247_);
lean_ctor_set(v_msg_268_, 1, v_msg_249_);
lean_ctor_set(v_msg_268_, 2, v___x_267_);
v___x_269_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msg_268_, v___x_260_, v___y_251_);
lean_dec_ref_known(v___x_260_, 3);
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_308_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_308_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_308_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v_traceState_275_; lean_object* v_env_276_; lean_object* v_nextMacroScope_277_; lean_object* v_ngen_278_; lean_object* v_auxDeclNGen_279_; lean_object* v_cache_280_; lean_object* v_recordedDeps_281_; lean_object* v_messages_282_; lean_object* v_infoState_283_; lean_object* v_snapshotTasks_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_307_; 
v___x_274_ = lean_st_ref_take(v___y_251_);
v_traceState_275_ = lean_ctor_get(v___x_274_, 4);
v_env_276_ = lean_ctor_get(v___x_274_, 0);
v_nextMacroScope_277_ = lean_ctor_get(v___x_274_, 1);
v_ngen_278_ = lean_ctor_get(v___x_274_, 2);
v_auxDeclNGen_279_ = lean_ctor_get(v___x_274_, 3);
v_cache_280_ = lean_ctor_get(v___x_274_, 5);
v_recordedDeps_281_ = lean_ctor_get(v___x_274_, 6);
v_messages_282_ = lean_ctor_get(v___x_274_, 7);
v_infoState_283_ = lean_ctor_get(v___x_274_, 8);
v_snapshotTasks_284_ = lean_ctor_get(v___x_274_, 9);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_307_ == 0)
{
v___x_286_ = v___x_274_;
v_isShared_287_ = v_isSharedCheck_307_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snapshotTasks_284_);
lean_inc(v_infoState_283_);
lean_inc(v_messages_282_);
lean_inc(v_recordedDeps_281_);
lean_inc(v_cache_280_);
lean_inc(v_traceState_275_);
lean_inc(v_auxDeclNGen_279_);
lean_inc(v_ngen_278_);
lean_inc(v_nextMacroScope_277_);
lean_inc(v_env_276_);
lean_dec(v___x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_307_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint64_t v_tid_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_305_; 
v_tid_288_ = lean_ctor_get_uint64(v_traceState_275_, sizeof(void*)*1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_traceState_275_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_traceState_275_, 0);
lean_dec(v_unused_306_);
v___x_290_ = v_traceState_275_;
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
else
{
lean_dec(v_traceState_275_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ref_248_);
lean_ctor_set(v___x_293_, 1, v_a_270_);
v___x_294_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_246_, v___x_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_294_);
lean_ctor_set_uint64(v_reuseFailAlloc_304_, sizeof(void*)*1, v_tid_288_);
v___x_296_ = v_reuseFailAlloc_304_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 4, v___x_296_);
v___x_298_ = v___x_286_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_env_276_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_nextMacroScope_277_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_ngen_278_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_auxDeclNGen_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_cache_280_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_recordedDeps_281_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_messages_282_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_infoState_283_);
lean_ctor_set(v_reuseFailAlloc_303_, 9, v_snapshotTasks_284_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_st_ref_put(v___y_251_, v___x_298_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_292_);
v___x_301_ = v___x_272_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_292_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_246_ = stack[0].m_obj;
lean_object* v_data_247_ = stack[1].m_obj;
lean_object* v_ref_248_ = stack[2].m_obj;
lean_object* v_msg_249_ = stack[3].m_obj;
lean_object* v___y_250_ = stack[4].m_obj;
lean_object* v___y_251_ = stack[5].m_obj;
lean_object* v_res_309_;
v_res_309_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_246_, v_data_247_, v_ref_248_, v_msg_249_, v___y_250_, v___y_251_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object* v_oldTraces_310_, lean_object* v_data_311_, lean_object* v_ref_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_310_, v_data_311_, v_ref_312_, v_msg_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0(void){
_start:
{
lean_object* v___x_318_; double v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_float_of_nat(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3(void){
_start:
{
lean_object* v___x_323_; double v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1000u);
v___x_324_ = lean_float_of_nat(v___x_323_);
return v___x_324_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_325_, uint8_t v_collapsed_326_, lean_object* v_tag_327_, lean_object* v_opts_328_, uint8_t v_clsEnabled_329_, lean_object* v_oldTraces_330_, lean_object* v_msg_331_, lean_object* v_resStartStop_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v_data_341_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___y_349_; lean_object* v_a_350_; uint8_t v___y_365_; double v___y_397_; 
v_fst_336_ = lean_ctor_get(v_resStartStop_332_, 0);
lean_inc(v_fst_336_);
v_snd_337_ = lean_ctor_get(v_resStartStop_332_, 1);
lean_inc(v_snd_337_);
lean_dec_ref(v_resStartStop_332_);
v_fst_344_ = lean_ctor_get(v_snd_337_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v_snd_337_, 1);
lean_inc(v_snd_345_);
lean_dec(v_snd_337_);
v___x_346_ = l_Lean_trace_profiler;
v___x_347_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_328_, v___x_346_);
if (v___x_347_ == 0)
{
v___y_365_ = v___x_347_;
goto v___jp_364_;
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = l_Lean_trace_profiler_useHeartbeats;
v___x_403_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_328_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; double v___x_406_; double v___x_407_; double v___x_408_; 
v___x_404_ = l_Lean_trace_profiler_threshold;
v___x_405_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_328_, v___x_404_);
v___x_406_ = lean_float_of_nat(v___x_405_);
v___x_407_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3);
v___x_408_ = lean_float_div(v___x_406_, v___x_407_);
v___y_397_ = v___x_408_;
goto v___jp_396_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; double v___x_411_; 
v___x_409_ = l_Lean_trace_profiler_threshold;
v___x_410_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_328_, v___x_409_);
v___x_411_ = lean_float_of_nat(v___x_410_);
v___y_397_ = v___x_411_;
goto v___jp_396_;
}
}
v___jp_338_:
{
lean_object* v___x_342_; 
lean_inc(v___y_339_);
v___x_342_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_330_, v_data_341_, v___y_339_, v___y_340_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_343_; 
lean_dec_ref_known(v___x_342_, 1);
v___x_343_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_336_);
return v___x_343_;
}
else
{
lean_dec(v_fst_336_);
return v___x_342_;
}
}
v___jp_348_:
{
uint8_t v_result_351_; lean_object* v___x_352_; lean_object* v___x_353_; double v___x_354_; lean_object* v_data_355_; 
v_result_351_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_fst_336_);
v___x_352_ = lean_box(v_result_351_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
v___x_354_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0);
lean_inc_ref(v_tag_327_);
lean_inc_ref(v___x_353_);
lean_inc(v_cls_325_);
v_data_355_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_355_, 0, v_cls_325_);
lean_ctor_set(v_data_355_, 1, v___x_353_);
lean_ctor_set(v_data_355_, 2, v_tag_327_);
lean_ctor_set_float(v_data_355_, sizeof(void*)*3, v___x_354_);
lean_ctor_set_float(v_data_355_, sizeof(void*)*3 + 8, v___x_354_);
lean_ctor_set_uint8(v_data_355_, sizeof(void*)*3 + 16, v_collapsed_326_);
if (v___x_347_ == 0)
{
lean_dec_ref_known(v___x_353_, 1);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec_ref(v_tag_327_);
lean_dec(v_cls_325_);
v___y_339_ = v___y_349_;
v___y_340_ = v_a_350_;
v_data_341_ = v_data_355_;
goto v___jp_338_;
}
else
{
lean_object* v_data_356_; double v___x_357_; double v___x_358_; 
lean_dec_ref_known(v_data_355_, 3);
v_data_356_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_356_, 0, v_cls_325_);
lean_ctor_set(v_data_356_, 1, v___x_353_);
lean_ctor_set(v_data_356_, 2, v_tag_327_);
v___x_357_ = lean_unbox_float(v_fst_344_);
lean_dec(v_fst_344_);
lean_ctor_set_float(v_data_356_, sizeof(void*)*3, v___x_357_);
v___x_358_ = lean_unbox_float(v_snd_345_);
lean_dec(v_snd_345_);
lean_ctor_set_float(v_data_356_, sizeof(void*)*3 + 8, v___x_358_);
lean_ctor_set_uint8(v_data_356_, sizeof(void*)*3 + 16, v_collapsed_326_);
v___y_339_ = v___y_349_;
v___y_340_ = v_a_350_;
v_data_341_ = v_data_356_;
goto v___jp_338_;
}
}
v___jp_359_:
{
lean_object* v_ref_360_; lean_object* v___x_361_; 
v_ref_360_ = lean_ctor_get(v___y_333_, 2);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
lean_inc(v_fst_336_);
v___x_361_ = lean_apply_4(v_msg_331_, v_fst_336_, v___y_333_, v___y_334_, lean_box(0));
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___y_349_ = v_ref_360_;
v_a_350_ = v_a_362_;
goto v___jp_348_;
}
else
{
lean_object* v___x_363_; 
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2);
v___y_349_ = v_ref_360_;
v_a_350_ = v___x_363_;
goto v___jp_348_;
}
}
v___jp_364_:
{
if (v_clsEnabled_329_ == 0)
{
if (v___y_365_ == 0)
{
lean_object* v___x_366_; lean_object* v_traceState_367_; lean_object* v_env_368_; lean_object* v_nextMacroScope_369_; lean_object* v_ngen_370_; lean_object* v_auxDeclNGen_371_; lean_object* v_cache_372_; lean_object* v_recordedDeps_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec_ref(v_msg_331_);
lean_dec_ref(v_tag_327_);
lean_dec(v_cls_325_);
v___x_366_ = lean_st_ref_take(v___y_334_);
v_traceState_367_ = lean_ctor_get(v___x_366_, 4);
v_env_368_ = lean_ctor_get(v___x_366_, 0);
v_nextMacroScope_369_ = lean_ctor_get(v___x_366_, 1);
v_ngen_370_ = lean_ctor_get(v___x_366_, 2);
v_auxDeclNGen_371_ = lean_ctor_get(v___x_366_, 3);
v_cache_372_ = lean_ctor_get(v___x_366_, 5);
v_recordedDeps_373_ = lean_ctor_get(v___x_366_, 6);
v_messages_374_ = lean_ctor_get(v___x_366_, 7);
v_infoState_375_ = lean_ctor_get(v___x_366_, 8);
v_snapshotTasks_376_ = lean_ctor_get(v___x_366_, 9);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_395_ == 0)
{
v___x_378_ = v___x_366_;
v_isShared_379_ = v_isSharedCheck_395_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_recordedDeps_373_);
lean_inc(v_cache_372_);
lean_inc(v_traceState_367_);
lean_inc(v_auxDeclNGen_371_);
lean_inc(v_ngen_370_);
lean_inc(v_nextMacroScope_369_);
lean_inc(v_env_368_);
lean_dec(v___x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_395_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint64_t v_tid_380_; lean_object* v_traces_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_394_; 
v_tid_380_ = lean_ctor_get_uint64(v_traceState_367_, sizeof(void*)*1);
v_traces_381_ = lean_ctor_get(v_traceState_367_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_traceState_367_);
if (v_isSharedCheck_394_ == 0)
{
v___x_383_ = v_traceState_367_;
v_isShared_384_ = v_isSharedCheck_394_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_traces_381_);
lean_dec(v_traceState_367_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_394_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_330_, v_traces_381_);
lean_dec_ref(v_traces_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_385_);
lean_ctor_set_uint64(v_reuseFailAlloc_393_, sizeof(void*)*1, v_tid_380_);
v___x_387_ = v_reuseFailAlloc_393_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 4, v___x_387_);
v___x_389_ = v___x_378_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_env_368_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_auxDeclNGen_371_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 6, v_recordedDeps_373_);
lean_ctor_set(v_reuseFailAlloc_392_, 7, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_392_, 8, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_392_, 9, v_snapshotTasks_376_);
v___x_389_ = v_reuseFailAlloc_392_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_st_ref_put(v___y_334_, v___x_389_);
v___x_391_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_336_);
return v___x_391_;
}
}
}
}
}
else
{
goto v___jp_359_;
}
}
else
{
goto v___jp_359_;
}
}
v___jp_396_:
{
double v___x_398_; double v___x_399_; double v___x_400_; uint8_t v___x_401_; 
v___x_398_ = lean_unbox_float(v_snd_345_);
v___x_399_ = lean_unbox_float(v_fst_344_);
v___x_400_ = lean_float_sub(v___x_398_, v___x_399_);
v___x_401_ = lean_float_decLt(v___y_397_, v___x_400_);
v___y_365_ = v___x_401_;
goto v___jp_364_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_325_ = stack[0].m_obj;
uint8_t v_collapsed_326_ = stack[1].m_num;
lean_object* v_tag_327_ = stack[2].m_obj;
lean_object* v_opts_328_ = stack[3].m_obj;
uint8_t v_clsEnabled_329_ = stack[4].m_num;
lean_object* v_oldTraces_330_ = stack[5].m_obj;
lean_object* v_msg_331_ = stack[6].m_obj;
lean_object* v_resStartStop_332_ = stack[7].m_obj;
lean_object* v___y_333_ = stack[8].m_obj;
lean_object* v___y_334_ = stack[9].m_obj;
lean_object* v_res_412_;
v_res_412_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_325_, v_collapsed_326_, v_tag_327_, v_opts_328_, v_clsEnabled_329_, v_oldTraces_330_, v_msg_331_, v_resStartStop_332_, v___y_333_, v___y_334_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_413_, lean_object* v_collapsed_414_, lean_object* v_tag_415_, lean_object* v_opts_416_, lean_object* v_clsEnabled_417_, lean_object* v_oldTraces_418_, lean_object* v_msg_419_, lean_object* v_resStartStop_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_collapsed_boxed_424_; uint8_t v_clsEnabled_boxed_425_; lean_object* v_res_426_; 
v_collapsed_boxed_424_ = lean_unbox(v_collapsed_414_);
v_clsEnabled_boxed_425_ = lean_unbox(v_clsEnabled_417_);
v_res_426_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_413_, v_collapsed_boxed_424_, v_tag_415_, v_opts_416_, v_clsEnabled_boxed_425_, v_oldTraces_418_, v_msg_419_, v_resStartStop_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec_ref(v_opts_416_);
return v_res_426_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_o_430_, lean_object* v_k_431_, uint8_t v_v_432_){
_start:
{
lean_object* v_map_433_; uint8_t v_hasTrace_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_448_; 
v_map_433_ = lean_ctor_get(v_o_430_, 0);
v_hasTrace_434_ = lean_ctor_get_uint8(v_o_430_, sizeof(void*)*1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_o_430_);
if (v_isSharedCheck_448_ == 0)
{
v___x_436_ = v_o_430_;
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_map_433_);
lean_dec(v_o_430_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_438_, 0, v_v_432_);
lean_inc(v_k_431_);
v___x_439_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_431_, v___x_438_, v_map_433_);
if (v_hasTrace_434_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_443_; 
v___x_440_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
v___x_441_ = l_Lean_Name_isPrefixOf(v___x_440_, v_k_431_);
lean_dec(v_k_431_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_443_ = v___x_436_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_439_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*1, v___x_441_);
return v___x_443_;
}
}
else
{
lean_object* v___x_446_; 
lean_dec(v_k_431_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_446_ = v___x_436_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*1, v_hasTrace_434_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_430_ = stack[0].m_obj;
lean_object* v_k_431_ = stack[1].m_obj;
uint8_t v_v_432_ = stack[2].m_num;
lean_object* v_res_449_;
v_res_449_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_o_430_, v_k_431_, v_v_432_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_o_450_, lean_object* v_k_451_, lean_object* v_v_452_){
_start:
{
uint8_t v_v_boxed_453_; lean_object* v_res_454_; 
v_v_boxed_453_ = lean_unbox(v_v_452_);
v_res_454_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_o_450_, v_k_451_, v_v_boxed_453_);
return v_res_454_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(lean_object* v_opts_455_, lean_object* v_opt_456_, uint8_t v_val_457_){
_start:
{
lean_object* v_name_458_; lean_object* v___x_459_; 
v_name_458_ = lean_ctor_get(v_opt_456_, 0);
lean_inc(v_name_458_);
lean_dec_ref(v_opt_456_);
v___x_459_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_opts_455_, v_name_458_, v_val_457_);
return v___x_459_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_455_ = stack[0].m_obj;
lean_object* v_opt_456_ = stack[1].m_obj;
uint8_t v_val_457_ = stack[2].m_num;
lean_object* v_res_460_;
v_res_460_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_opts_455_, v_opt_456_, v_val_457_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_opts_461_, lean_object* v_opt_462_, lean_object* v_val_463_){
_start:
{
uint8_t v_val_boxed_464_; lean_object* v_res_465_; 
v_val_boxed_464_ = lean_unbox(v_val_463_);
v_res_465_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_opts_461_, v_opt_462_, v_val_boxed_464_);
return v_res_465_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_466_; double v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1000000000u);
v___x_467_ = lean_float_of_nat(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_472_, uint8_t v___x_473_, lean_object* v___x_474_, lean_object* v___f_475_, lean_object* v_declNames_476_, lean_object* v___x_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; lean_object* v_a_488_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___y_503_; lean_object* v_a_504_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; uint8_t v___y_520_; lean_object* v___y_562_; uint16_t v___y_563_; lean_object* v_fileName_564_; lean_object* v_fileMap_565_; lean_object* v_currNamespace_566_; lean_object* v_openDecls_567_; lean_object* v_initHeartbeats_568_; lean_object* v_maxHeartbeats_569_; lean_object* v_quotContext_570_; lean_object* v_currMacroScope_571_; lean_object* v_cancelTk_x3f_572_; lean_object* v_inheritedTraceOptions_573_; lean_object* v_currRecDepth_574_; lean_object* v_ref_575_; uint8_t v_suppressElabErrors_576_; uint8_t v_isRecordingDeps_577_; lean_object* v___y_578_; lean_object* v_toCold_591_; lean_object* v_currRecDepth_592_; lean_object* v_ref_593_; uint8_t v_suppressElabErrors_594_; uint8_t v_isRecordingDeps_595_; lean_object* v_fileName_596_; lean_object* v_fileMap_597_; lean_object* v_options_598_; lean_object* v_currNamespace_599_; lean_object* v_openDecls_600_; lean_object* v_initHeartbeats_601_; lean_object* v_maxHeartbeats_602_; lean_object* v_quotContext_603_; lean_object* v_currMacroScope_604_; lean_object* v_cancelTk_x3f_605_; lean_object* v_inheritedTraceOptions_606_; lean_object* v___y_608_; uint8_t v___y_609_; uint16_t v___y_610_; lean_object* v___y_633_; 
v_toCold_591_ = lean_ctor_get(v___y_478_, 0);
lean_inc_ref(v_toCold_591_);
v_currRecDepth_592_ = lean_ctor_get(v___y_478_, 1);
lean_inc(v_currRecDepth_592_);
v_ref_593_ = lean_ctor_get(v___y_478_, 2);
lean_inc(v_ref_593_);
v_suppressElabErrors_594_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 2);
v_isRecordingDeps_595_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_478_);
v_fileName_596_ = lean_ctor_get(v_toCold_591_, 0);
lean_inc_ref(v_fileName_596_);
v_fileMap_597_ = lean_ctor_get(v_toCold_591_, 1);
lean_inc_ref(v_fileMap_597_);
v_options_598_ = lean_ctor_get(v_toCold_591_, 2);
lean_inc_ref(v_options_598_);
v_currNamespace_599_ = lean_ctor_get(v_toCold_591_, 4);
lean_inc(v_currNamespace_599_);
v_openDecls_600_ = lean_ctor_get(v_toCold_591_, 5);
lean_inc(v_openDecls_600_);
v_initHeartbeats_601_ = lean_ctor_get(v_toCold_591_, 6);
lean_inc(v_initHeartbeats_601_);
v_maxHeartbeats_602_ = lean_ctor_get(v_toCold_591_, 7);
lean_inc(v_maxHeartbeats_602_);
v_quotContext_603_ = lean_ctor_get(v_toCold_591_, 8);
lean_inc(v_quotContext_603_);
v_currMacroScope_604_ = lean_ctor_get(v_toCold_591_, 9);
lean_inc(v_currMacroScope_604_);
v_cancelTk_x3f_605_ = lean_ctor_get(v_toCold_591_, 10);
lean_inc(v_cancelTk_x3f_605_);
v_inheritedTraceOptions_606_ = lean_ctor_get(v_toCold_591_, 11);
lean_inc_ref(v_inheritedTraceOptions_606_);
lean_dec_ref(v_toCold_591_);
if (v_isRecordingDeps_595_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_644_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_options_598_, v___x_643_, v_isRecordingDeps_595_);
v___y_633_ = v___x_644_;
goto v___jp_632_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_598_);
v___y_633_ = v___x_645_;
goto v___jp_632_;
}
v___jp_481_:
{
lean_object* v___x_489_; double v___x_490_; double v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_489_ = lean_io_get_num_heartbeats();
v___x_490_ = lean_float_of_nat(v___y_486_);
v___x_491_ = lean_float_of_nat(v___x_489_);
v___x_492_ = lean_box_float(v___x_490_);
v___x_493_ = lean_box_float(v___x_491_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_a_488_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_472_, v___x_473_, v___x_474_, v___y_484_, v___y_487_, v___y_485_, v___f_475_, v___x_495_, v___y_482_, v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v___y_484_);
return v___x_496_;
}
v___jp_497_:
{
lean_object* v___x_505_; double v___x_506_; double v___x_507_; double v___x_508_; double v___x_509_; double v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_505_ = lean_io_mono_nanos_now();
v___x_506_ = lean_float_of_nat(v___y_499_);
v___x_507_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_508_ = lean_float_div(v___x_506_, v___x_507_);
v___x_509_ = lean_float_of_nat(v___x_505_);
v___x_510_ = lean_float_div(v___x_509_, v___x_507_);
v___x_511_ = lean_box_float(v___x_508_);
v___x_512_ = lean_box_float(v___x_510_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_a_504_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_472_, v___x_473_, v___x_474_, v___y_501_, v___y_503_, v___y_502_, v___f_475_, v___x_514_, v___y_498_, v___y_500_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v___y_501_);
return v___x_515_;
}
v___jp_516_:
{
lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_518_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = l_Lean_trace_profiler_useHeartbeats;
v___x_524_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_519_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_io_mono_nanos_now();
v___x_526_ = l_Lean_Compiler_LCNF_main(v_declNames_476_, v___x_477_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 1);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_498_ = v___y_517_;
v___y_499_ = v___x_525_;
v___y_500_ = v___y_518_;
v___y_501_ = v___y_519_;
v___y_502_ = v_a_522_;
v___y_503_ = v___y_520_;
v_a_504_ = v___x_532_;
goto v___jp_497_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_526_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_526_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v___y_498_ = v___y_517_;
v___y_499_ = v___x_525_;
v___y_500_ = v___y_518_;
v___y_501_ = v___y_519_;
v___y_502_ = v_a_522_;
v___y_503_ = v___y_520_;
v_a_504_ = v___x_540_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = l_Lean_Compiler_LCNF_main(v_declNames_476_, v___x_477_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v___y_482_ = v___y_517_;
v___y_483_ = v___y_518_;
v___y_484_ = v___y_519_;
v___y_485_ = v_a_522_;
v___y_486_ = v___x_543_;
v___y_487_ = v___y_520_;
v_a_488_ = v___x_550_;
goto v___jp_481_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 0);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v___y_482_ = v___y_517_;
v___y_483_ = v___y_518_;
v___y_484_ = v___y_519_;
v___y_485_ = v_a_522_;
v___y_486_ = v___x_543_;
v___y_487_ = v___y_520_;
v_a_488_ = v___x_558_;
goto v___jp_481_;
}
}
}
}
}
v___jp_561_:
{
uint8_t v_hasTrace_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_hasTrace_579_ = lean_ctor_get_uint8(v___y_562_, sizeof(void*)*1);
v___x_580_ = l_Lean_maxRecDepth;
v___x_581_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v___y_562_, v___x_580_);
lean_inc_ref(v_inheritedTraceOptions_573_);
lean_inc_ref(v___y_562_);
v___x_582_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_582_, 0, v_fileName_564_);
lean_ctor_set(v___x_582_, 1, v_fileMap_565_);
lean_ctor_set(v___x_582_, 2, v___y_562_);
lean_ctor_set(v___x_582_, 3, v___x_581_);
lean_ctor_set(v___x_582_, 4, v_currNamespace_566_);
lean_ctor_set(v___x_582_, 5, v_openDecls_567_);
lean_ctor_set(v___x_582_, 6, v_initHeartbeats_568_);
lean_ctor_set(v___x_582_, 7, v_maxHeartbeats_569_);
lean_ctor_set(v___x_582_, 8, v_quotContext_570_);
lean_ctor_set(v___x_582_, 9, v_currMacroScope_571_);
lean_ctor_set(v___x_582_, 10, v_cancelTk_x3f_572_);
lean_ctor_set(v___x_582_, 11, v_inheritedTraceOptions_573_);
v___x_583_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_currRecDepth_574_);
lean_ctor_set(v___x_583_, 2, v_ref_575_);
lean_ctor_set_uint16(v___x_583_, sizeof(void*)*3, v___y_563_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3 + 2, v_suppressElabErrors_576_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3 + 3, v_isRecordingDeps_577_);
if (v_hasTrace_579_ == 0)
{
lean_object* v___x_584_; 
lean_dec_ref(v_inheritedTraceOptions_573_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___f_475_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_472_);
v___x_584_ = l_Lean_Compiler_LCNF_main(v_declNames_476_, v___x_477_, v___x_583_, v___y_578_);
lean_dec_ref_known(v___x_583_, 3);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
lean_inc(v___x_472_);
v___x_586_ = l_Lean_Name_append(v___x_585_, v___x_472_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_573_, v___y_562_, v___x_586_);
lean_dec(v___x_586_);
lean_dec_ref(v_inheritedTraceOptions_573_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = l_Lean_trace_profiler;
v___x_589_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_562_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v___y_562_);
lean_dec_ref(v___f_475_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_472_);
v___x_590_ = l_Lean_Compiler_LCNF_main(v_declNames_476_, v___x_477_, v___x_583_, v___y_578_);
lean_dec_ref_known(v___x_583_, 3);
return v___x_590_;
}
else
{
v___y_517_ = v___x_583_;
v___y_518_ = v___y_578_;
v___y_519_ = v___y_562_;
v___y_520_ = v___x_587_;
goto v___jp_516_;
}
}
else
{
v___y_517_ = v___x_583_;
v___y_518_ = v___y_578_;
v___y_519_ = v___y_562_;
v___y_520_ = v___x_587_;
goto v___jp_516_;
}
}
}
v___jp_607_:
{
lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v_nextMacroScope_613_; lean_object* v_ngen_614_; lean_object* v_auxDeclNGen_615_; lean_object* v_traceState_616_; lean_object* v_recordedDeps_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_630_; 
v___x_611_ = lean_st_ref_take(v___y_479_);
v_env_612_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_613_ = lean_ctor_get(v___x_611_, 1);
v_ngen_614_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_615_ = lean_ctor_get(v___x_611_, 3);
v_traceState_616_ = lean_ctor_get(v___x_611_, 4);
v_recordedDeps_617_ = lean_ctor_get(v___x_611_, 6);
v_messages_618_ = lean_ctor_get(v___x_611_, 7);
v_infoState_619_ = lean_ctor_get(v___x_611_, 8);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 9);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_611_, 5);
lean_dec(v_unused_631_);
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_recordedDeps_617_);
lean_inc(v_traceState_616_);
lean_inc(v_auxDeclNGen_615_);
lean_inc(v_ngen_614_);
lean_inc(v_nextMacroScope_613_);
lean_inc(v_env_612_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = l_Lean_Kernel_enableDiag(v_env_612_, v___y_609_);
v___x_625_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 5, v___x_625_);
lean_ctor_set(v___x_622_, 0, v___x_624_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_nextMacroScope_613_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_ngen_614_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_auxDeclNGen_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_traceState_616_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_629_, 6, v_recordedDeps_617_);
lean_ctor_set(v_reuseFailAlloc_629_, 7, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_629_, 8, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_629_, 9, v_snapshotTasks_620_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_st_ref_put(v___y_479_, v___x_627_);
v___y_562_ = v___y_608_;
v___y_563_ = v___y_610_;
v_fileName_564_ = v_fileName_596_;
v_fileMap_565_ = v_fileMap_597_;
v_currNamespace_566_ = v_currNamespace_599_;
v_openDecls_567_ = v_openDecls_600_;
v_initHeartbeats_568_ = v_initHeartbeats_601_;
v_maxHeartbeats_569_ = v_maxHeartbeats_602_;
v_quotContext_570_ = v_quotContext_603_;
v_currMacroScope_571_ = v_currMacroScope_604_;
v_cancelTk_x3f_572_ = v_cancelTk_x3f_605_;
v_inheritedTraceOptions_573_ = v_inheritedTraceOptions_606_;
v_currRecDepth_574_ = v_currRecDepth_592_;
v_ref_575_ = v_ref_593_;
v_suppressElabErrors_576_ = v_suppressElabErrors_594_;
v_isRecordingDeps_577_ = v_isRecordingDeps_595_;
v___y_578_ = v___y_479_;
goto v___jp_561_;
}
}
}
v___jp_632_:
{
uint16_t v___x_634_; lean_object* v___x_635_; lean_object* v_env_636_; uint8_t v___x_637_; uint16_t v___x_638_; uint16_t v___x_639_; uint16_t v___x_640_; uint8_t v___x_641_; 
v___x_634_ = l_Lean_OptionFlags_ofOptions(v___y_633_);
v___x_635_ = lean_st_ref_get(v___y_479_);
v_env_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_635_);
v___x_637_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_636_);
lean_dec_ref(v_env_636_);
v___x_638_ = 512;
v___x_639_ = lean_uint16_land(v___x_634_, v___x_638_);
v___x_640_ = 0;
v___x_641_ = lean_uint16_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
if (v___x_637_ == 0)
{
v___y_608_ = v___y_633_;
v___y_609_ = v___x_473_;
v___y_610_ = v___x_634_;
goto v___jp_607_;
}
else
{
v___y_562_ = v___y_633_;
v___y_563_ = v___x_634_;
v_fileName_564_ = v_fileName_596_;
v_fileMap_565_ = v_fileMap_597_;
v_currNamespace_566_ = v_currNamespace_599_;
v_openDecls_567_ = v_openDecls_600_;
v_initHeartbeats_568_ = v_initHeartbeats_601_;
v_maxHeartbeats_569_ = v_maxHeartbeats_602_;
v_quotContext_570_ = v_quotContext_603_;
v_currMacroScope_571_ = v_currMacroScope_604_;
v_cancelTk_x3f_572_ = v_cancelTk_x3f_605_;
v_inheritedTraceOptions_573_ = v_inheritedTraceOptions_606_;
v_currRecDepth_574_ = v_currRecDepth_592_;
v_ref_575_ = v_ref_593_;
v_suppressElabErrors_576_ = v_suppressElabErrors_594_;
v_isRecordingDeps_577_ = v_isRecordingDeps_595_;
v___y_578_ = v___y_479_;
goto v___jp_561_;
}
}
else
{
if (v___x_637_ == 0)
{
v___y_562_ = v___y_633_;
v___y_563_ = v___x_634_;
v_fileName_564_ = v_fileName_596_;
v_fileMap_565_ = v_fileMap_597_;
v_currNamespace_566_ = v_currNamespace_599_;
v_openDecls_567_ = v_openDecls_600_;
v_initHeartbeats_568_ = v_initHeartbeats_601_;
v_maxHeartbeats_569_ = v_maxHeartbeats_602_;
v_quotContext_570_ = v_quotContext_603_;
v_currMacroScope_571_ = v_currMacroScope_604_;
v_cancelTk_x3f_572_ = v_cancelTk_x3f_605_;
v_inheritedTraceOptions_573_ = v_inheritedTraceOptions_606_;
v_currRecDepth_574_ = v_currRecDepth_592_;
v_ref_575_ = v_ref_593_;
v_suppressElabErrors_576_ = v_suppressElabErrors_594_;
v_isRecordingDeps_577_ = v_isRecordingDeps_595_;
v___y_578_ = v___y_479_;
goto v___jp_561_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = 0;
v___y_608_ = v___y_633_;
v___y_609_ = v___x_642_;
v___y_610_ = v___x_634_;
goto v___jp_607_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_compile___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_472_ = stack[0].m_obj;
uint8_t v___x_473_ = stack[1].m_num;
lean_object* v___x_474_ = stack[2].m_obj;
lean_object* v___f_475_ = stack[3].m_obj;
lean_object* v_declNames_476_ = stack[4].m_obj;
lean_object* v___x_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v___y_479_ = stack[7].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Lean_Compiler_compile___lam__1(v___x_472_, v___x_473_, v___x_474_, v___f_475_, v_declNames_476_, v___x_477_, v___y_478_, v___y_479_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v___f_650_, lean_object* v_declNames_651_, lean_object* v___x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
uint8_t v___x_7421__boxed_656_; lean_object* v_res_657_; 
v___x_7421__boxed_656_ = lean_unbox(v___x_648_);
v_res_657_ = l_Lean_Compiler_compile___lam__1(v___x_647_, v___x_7421__boxed_656_, v___x_649_, v___f_650_, v_declNames_651_, v___x_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
return v_res_657_;
}
}
lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___f_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc_ref(v_declNames_663_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_667_, 0, v_declNames_663_);
v___x_668_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_664_);
v___x_669_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_670_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_671_ = l_Lean_Options_empty;
v___x_672_ = 1;
v___x_673_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_674_ = lean_box(v___x_672_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_675_, 0, v___x_670_);
lean_closure_set(v___f_675_, 1, v___x_674_);
lean_closure_set(v___f_675_, 2, v___x_673_);
lean_closure_set(v___f_675_, 3, v___f_667_);
lean_closure_set(v___f_675_, 4, v_declNames_663_);
lean_closure_set(v___f_675_, 5, v___x_671_);
v___x_676_ = lean_box(0);
v___x_677_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_669_, v___x_668_, v___f_675_, v___x_676_, v_a_664_, v_a_665_);
lean_dec_ref(v___x_668_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Compiler_compile_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_663_ = stack[0].m_obj;
lean_object* v_a_664_ = stack[1].m_obj;
lean_object* v_a_665_ = stack[2].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Compiler_compile(v_declNames_663_, v_a_664_, v_a_665_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Compiler_compile(v_declNames_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_683_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object* v_00_u03b1_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_685_);
return v___x_689_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_685_ = stack[1].m_obj;
lean_object* v___y_686_ = stack[2].m_obj;
lean_object* v___y_687_ = stack[3].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_box(0), v_x_685_, v___y_686_, v___y_687_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_00_u03b1_691_, v_x_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
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
lean_dec_ref_known(v___x_760_, 1);
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
LEAN_EXPORT void l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_763_;
v_res_763_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_765_;
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

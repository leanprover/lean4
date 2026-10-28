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
lean_object* v_toCold_243_; lean_object* v_currRecDepth_244_; lean_object* v_ref_245_; uint16_t v_optionFlags_246_; uint8_t v_suppressElabErrors_247_; uint8_t v_checkDeprecated_248_; uint8_t v_isRecordingDeps_249_; lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_traceState_253_; lean_object* v_traces_254_; lean_object* v___x_255_; size_t v_sz_256_; size_t v___x_257_; lean_object* v___x_258_; lean_object* v_msg_259_; lean_object* v___x_260_; lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_299_; 
v_toCold_243_ = lean_ctor_get(v___y_240_, 0);
v_currRecDepth_244_ = lean_ctor_get(v___y_240_, 1);
v_ref_245_ = lean_ctor_get(v___y_240_, 2);
v_optionFlags_246_ = lean_ctor_get_uint16(v___y_240_, sizeof(void*)*3);
v_suppressElabErrors_247_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*3 + 2);
v_checkDeprecated_248_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*3 + 3);
v_isRecordingDeps_249_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*3 + 4);
v_ref_250_ = l_Lean_replaceRef(v_ref_238_, v_ref_245_);
lean_inc(v_currRecDepth_244_);
lean_inc_ref(v_toCold_243_);
v___x_251_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_251_, 0, v_toCold_243_);
lean_ctor_set(v___x_251_, 1, v_currRecDepth_244_);
lean_ctor_set(v___x_251_, 2, v_ref_250_);
lean_ctor_set_uint16(v___x_251_, sizeof(void*)*3, v_optionFlags_246_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*3 + 2, v_suppressElabErrors_247_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*3 + 3, v_checkDeprecated_248_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*3 + 4, v_isRecordingDeps_249_);
v___x_252_ = lean_st_ref_get(v___y_241_);
v_traceState_253_ = lean_ctor_get(v___x_252_, 4);
lean_inc_ref(v_traceState_253_);
lean_dec(v___x_252_);
v_traces_254_ = lean_ctor_get(v_traceState_253_, 0);
lean_inc_ref(v_traces_254_);
lean_dec_ref(v_traceState_253_);
v___x_255_ = l_Lean_PersistentArray_toArray___redArg(v_traces_254_);
lean_dec_ref(v_traces_254_);
v_sz_256_ = lean_array_size(v___x_255_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__6(v_sz_256_, v___x_257_, v___x_255_);
v_msg_259_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_259_, 0, v_data_237_);
lean_ctor_set(v_msg_259_, 1, v_msg_239_);
lean_ctor_set(v_msg_259_, 2, v___x_258_);
v___x_260_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7(v_msg_259_, v___x_251_, v___y_241_);
lean_dec_ref_known(v___x_251_, 3);
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_299_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_299_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_299_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v_traceState_266_; lean_object* v_env_267_; lean_object* v_nextMacroScope_268_; lean_object* v_ngen_269_; lean_object* v_auxDeclNGen_270_; lean_object* v_cache_271_; lean_object* v_recordedDeps_272_; lean_object* v_messages_273_; lean_object* v_infoState_274_; lean_object* v_snapshotTasks_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_298_; 
v___x_265_ = lean_st_ref_take(v___y_241_);
v_traceState_266_ = lean_ctor_get(v___x_265_, 4);
v_env_267_ = lean_ctor_get(v___x_265_, 0);
v_nextMacroScope_268_ = lean_ctor_get(v___x_265_, 1);
v_ngen_269_ = lean_ctor_get(v___x_265_, 2);
v_auxDeclNGen_270_ = lean_ctor_get(v___x_265_, 3);
v_cache_271_ = lean_ctor_get(v___x_265_, 5);
v_recordedDeps_272_ = lean_ctor_get(v___x_265_, 6);
v_messages_273_ = lean_ctor_get(v___x_265_, 7);
v_infoState_274_ = lean_ctor_get(v___x_265_, 8);
v_snapshotTasks_275_ = lean_ctor_get(v___x_265_, 9);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_298_ == 0)
{
v___x_277_ = v___x_265_;
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snapshotTasks_275_);
lean_inc(v_infoState_274_);
lean_inc(v_messages_273_);
lean_inc(v_recordedDeps_272_);
lean_inc(v_cache_271_);
lean_inc(v_traceState_266_);
lean_inc(v_auxDeclNGen_270_);
lean_inc(v_ngen_269_);
lean_inc(v_nextMacroScope_268_);
lean_inc(v_env_267_);
lean_dec(v___x_265_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint64_t v_tid_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_296_; 
v_tid_279_ = lean_ctor_get_uint64(v_traceState_266_, sizeof(void*)*1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_traceState_266_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_traceState_266_, 0);
lean_dec(v_unused_297_);
v___x_281_ = v_traceState_266_;
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_traceState_266_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_ref_238_);
lean_ctor_set(v___x_284_, 1, v_a_261_);
v___x_285_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_236_, v___x_284_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_285_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_285_);
lean_ctor_set_uint64(v_reuseFailAlloc_295_, sizeof(void*)*1, v_tid_279_);
v___x_287_ = v_reuseFailAlloc_295_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_289_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 4, v___x_287_);
v___x_289_ = v___x_277_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_env_267_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_nextMacroScope_268_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_ngen_269_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_auxDeclNGen_270_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_294_, 5, v_cache_271_);
lean_ctor_set(v_reuseFailAlloc_294_, 6, v_recordedDeps_272_);
lean_ctor_set(v_reuseFailAlloc_294_, 7, v_messages_273_);
lean_ctor_set(v_reuseFailAlloc_294_, 8, v_infoState_274_);
lean_ctor_set(v_reuseFailAlloc_294_, 9, v_snapshotTasks_275_);
v___x_289_ = v_reuseFailAlloc_294_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_st_ref_put(v___y_241_, v___x_289_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_283_);
v___x_292_ = v___x_263_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_283_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4___boxed(lean_object* v_oldTraces_300_, lean_object* v_data_301_, lean_object* v_ref_302_, lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_300_, v_data_301_, v_ref_302_, v_msg_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_307_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0(void){
_start:
{
lean_object* v___x_308_; double v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_float_of_nat(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__1));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3(void){
_start:
{
lean_object* v___x_313_; double v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(1000u);
v___x_314_ = lean_float_of_nat(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(lean_object* v_cls_315_, uint8_t v_collapsed_316_, lean_object* v_tag_317_, lean_object* v_opts_318_, uint8_t v_clsEnabled_319_, lean_object* v_oldTraces_320_, lean_object* v_msg_321_, lean_object* v_resStartStop_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v_data_331_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___y_339_; lean_object* v_a_340_; uint8_t v___y_355_; double v___y_387_; 
v_fst_326_ = lean_ctor_get(v_resStartStop_322_, 0);
lean_inc(v_fst_326_);
v_snd_327_ = lean_ctor_get(v_resStartStop_322_, 1);
lean_inc(v_snd_327_);
lean_dec_ref(v_resStartStop_322_);
v_fst_334_ = lean_ctor_get(v_snd_327_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v_snd_327_, 1);
lean_inc(v_snd_335_);
lean_dec(v_snd_327_);
v___x_336_ = l_Lean_trace_profiler;
v___x_337_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_318_, v___x_336_);
if (v___x_337_ == 0)
{
v___y_355_ = v___x_337_;
goto v___jp_354_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = l_Lean_trace_profiler_useHeartbeats;
v___x_393_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_318_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; double v___x_396_; double v___x_397_; double v___x_398_; 
v___x_394_ = l_Lean_trace_profiler_threshold;
v___x_395_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_318_, v___x_394_);
v___x_396_ = lean_float_of_nat(v___x_395_);
v___x_397_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__3);
v___x_398_ = lean_float_div(v___x_396_, v___x_397_);
v___y_387_ = v___x_398_;
goto v___jp_386_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; double v___x_401_; 
v___x_399_ = l_Lean_trace_profiler_threshold;
v___x_400_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v_opts_318_, v___x_399_);
v___x_401_ = lean_float_of_nat(v___x_400_);
v___y_387_ = v___x_401_;
goto v___jp_386_;
}
}
v___jp_328_:
{
lean_object* v___x_332_; 
lean_inc(v___y_329_);
v___x_332_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4(v_oldTraces_320_, v_data_331_, v___y_329_, v___y_330_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
lean_dec_ref_known(v___x_332_, 1);
v___x_333_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_326_);
return v___x_333_;
}
else
{
lean_dec(v_fst_326_);
return v___x_332_;
}
}
v___jp_338_:
{
uint8_t v_result_341_; lean_object* v___x_342_; lean_object* v___x_343_; double v___x_344_; lean_object* v_data_345_; 
v_result_341_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__6(v_fst_326_);
v___x_342_ = lean_box(v_result_341_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
v___x_344_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__0);
lean_inc_ref(v_tag_317_);
lean_inc_ref(v___x_343_);
lean_inc(v_cls_315_);
v_data_345_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_345_, 0, v_cls_315_);
lean_ctor_set(v_data_345_, 1, v___x_343_);
lean_ctor_set(v_data_345_, 2, v_tag_317_);
lean_ctor_set_float(v_data_345_, sizeof(void*)*3, v___x_344_);
lean_ctor_set_float(v_data_345_, sizeof(void*)*3 + 8, v___x_344_);
lean_ctor_set_uint8(v_data_345_, sizeof(void*)*3 + 16, v_collapsed_316_);
if (v___x_337_ == 0)
{
lean_dec_ref_known(v___x_343_, 1);
lean_dec(v_snd_335_);
lean_dec(v_fst_334_);
lean_dec_ref(v_tag_317_);
lean_dec(v_cls_315_);
v___y_329_ = v___y_339_;
v___y_330_ = v_a_340_;
v_data_331_ = v_data_345_;
goto v___jp_328_;
}
else
{
lean_object* v_data_346_; double v___x_347_; double v___x_348_; 
lean_dec_ref_known(v_data_345_, 3);
v_data_346_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_346_, 0, v_cls_315_);
lean_ctor_set(v_data_346_, 1, v___x_343_);
lean_ctor_set(v_data_346_, 2, v_tag_317_);
v___x_347_ = lean_unbox_float(v_fst_334_);
lean_dec(v_fst_334_);
lean_ctor_set_float(v_data_346_, sizeof(void*)*3, v___x_347_);
v___x_348_ = lean_unbox_float(v_snd_335_);
lean_dec(v_snd_335_);
lean_ctor_set_float(v_data_346_, sizeof(void*)*3 + 8, v___x_348_);
lean_ctor_set_uint8(v_data_346_, sizeof(void*)*3 + 16, v_collapsed_316_);
v___y_329_ = v___y_339_;
v___y_330_ = v_a_340_;
v_data_331_ = v_data_346_;
goto v___jp_328_;
}
}
v___jp_349_:
{
lean_object* v_ref_350_; lean_object* v___x_351_; 
v_ref_350_ = lean_ctor_get(v___y_323_, 2);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
lean_inc(v_fst_326_);
v___x_351_ = lean_apply_4(v_msg_321_, v_fst_326_, v___y_323_, v___y_324_, lean_box(0));
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___y_339_ = v_ref_350_;
v_a_340_ = v_a_352_;
goto v___jp_338_;
}
else
{
lean_object* v___x_353_; 
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___closed__2);
v___y_339_ = v_ref_350_;
v_a_340_ = v___x_353_;
goto v___jp_338_;
}
}
v___jp_354_:
{
if (v_clsEnabled_319_ == 0)
{
if (v___y_355_ == 0)
{
lean_object* v___x_356_; lean_object* v_traceState_357_; lean_object* v_env_358_; lean_object* v_nextMacroScope_359_; lean_object* v_ngen_360_; lean_object* v_auxDeclNGen_361_; lean_object* v_cache_362_; lean_object* v_recordedDeps_363_; lean_object* v_messages_364_; lean_object* v_infoState_365_; lean_object* v_snapshotTasks_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_snd_335_);
lean_dec(v_fst_334_);
lean_dec_ref(v_msg_321_);
lean_dec_ref(v_tag_317_);
lean_dec(v_cls_315_);
v___x_356_ = lean_st_ref_take(v___y_324_);
v_traceState_357_ = lean_ctor_get(v___x_356_, 4);
v_env_358_ = lean_ctor_get(v___x_356_, 0);
v_nextMacroScope_359_ = lean_ctor_get(v___x_356_, 1);
v_ngen_360_ = lean_ctor_get(v___x_356_, 2);
v_auxDeclNGen_361_ = lean_ctor_get(v___x_356_, 3);
v_cache_362_ = lean_ctor_get(v___x_356_, 5);
v_recordedDeps_363_ = lean_ctor_get(v___x_356_, 6);
v_messages_364_ = lean_ctor_get(v___x_356_, 7);
v_infoState_365_ = lean_ctor_get(v___x_356_, 8);
v_snapshotTasks_366_ = lean_ctor_get(v___x_356_, 9);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_385_ == 0)
{
v___x_368_ = v___x_356_;
v_isShared_369_ = v_isSharedCheck_385_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snapshotTasks_366_);
lean_inc(v_infoState_365_);
lean_inc(v_messages_364_);
lean_inc(v_recordedDeps_363_);
lean_inc(v_cache_362_);
lean_inc(v_traceState_357_);
lean_inc(v_auxDeclNGen_361_);
lean_inc(v_ngen_360_);
lean_inc(v_nextMacroScope_359_);
lean_inc(v_env_358_);
lean_dec(v___x_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_385_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint64_t v_tid_370_; lean_object* v_traces_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_384_; 
v_tid_370_ = lean_ctor_get_uint64(v_traceState_357_, sizeof(void*)*1);
v_traces_371_ = lean_ctor_get(v_traceState_357_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_traceState_357_);
if (v_isSharedCheck_384_ == 0)
{
v___x_373_ = v_traceState_357_;
v_isShared_374_ = v_isSharedCheck_384_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_traces_371_);
lean_dec(v_traceState_357_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_384_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_320_, v_traces_371_);
lean_dec_ref(v_traces_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_375_);
lean_ctor_set_uint64(v_reuseFailAlloc_383_, sizeof(void*)*1, v_tid_370_);
v___x_377_ = v_reuseFailAlloc_383_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v___x_377_);
v___x_379_ = v___x_368_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_env_358_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_nextMacroScope_359_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_ngen_360_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_auxDeclNGen_361_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_382_, 5, v_cache_362_);
lean_ctor_set(v_reuseFailAlloc_382_, 6, v_recordedDeps_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 7, v_messages_364_);
lean_ctor_set(v_reuseFailAlloc_382_, 8, v_infoState_365_);
lean_ctor_set(v_reuseFailAlloc_382_, 9, v_snapshotTasks_366_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_st_ref_put(v___y_324_, v___x_379_);
v___x_381_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_fst_326_);
return v___x_381_;
}
}
}
}
}
else
{
goto v___jp_349_;
}
}
else
{
goto v___jp_349_;
}
}
v___jp_386_:
{
double v___x_388_; double v___x_389_; double v___x_390_; uint8_t v___x_391_; 
v___x_388_ = lean_unbox_float(v_snd_335_);
v___x_389_ = lean_unbox_float(v_fst_334_);
v___x_390_ = lean_float_sub(v___x_388_, v___x_389_);
v___x_391_ = lean_float_decLt(v___y_387_, v___x_390_);
v___y_355_ = v___x_391_;
goto v___jp_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_cls_402_, lean_object* v_collapsed_403_, lean_object* v_tag_404_, lean_object* v_opts_405_, lean_object* v_clsEnabled_406_, lean_object* v_oldTraces_407_, lean_object* v_msg_408_, lean_object* v_resStartStop_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
uint8_t v_collapsed_boxed_413_; uint8_t v_clsEnabled_boxed_414_; lean_object* v_res_415_; 
v_collapsed_boxed_413_ = lean_unbox(v_collapsed_403_);
v_clsEnabled_boxed_414_ = lean_unbox(v_clsEnabled_406_);
v_res_415_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v_cls_402_, v_collapsed_boxed_413_, v_tag_404_, v_opts_405_, v_clsEnabled_boxed_414_, v_oldTraces_407_, v_msg_408_, v_resStartStop_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec_ref(v_opts_405_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_o_419_, lean_object* v_k_420_, uint8_t v_v_421_){
_start:
{
lean_object* v_map_422_; uint8_t v_hasTrace_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_437_; 
v_map_422_ = lean_ctor_get(v_o_419_, 0);
v_hasTrace_423_ = lean_ctor_get_uint8(v_o_419_, sizeof(void*)*1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_o_419_);
if (v_isSharedCheck_437_ == 0)
{
v___x_425_ = v_o_419_;
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_map_422_);
lean_dec(v_o_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_427_, 0, v_v_421_);
lean_inc(v_k_420_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_420_, v___x_427_, v_map_422_);
if (v_hasTrace_423_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_432_; 
v___x_429_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
v___x_430_ = l_Lean_Name_isPrefixOf(v___x_429_, v_k_420_);
lean_dec(v_k_420_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_432_ = v___x_425_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_428_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_430_);
return v___x_432_;
}
}
else
{
lean_object* v___x_435_; 
lean_dec(v_k_420_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_435_ = v___x_425_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*1, v_hasTrace_423_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_o_438_, lean_object* v_k_439_, lean_object* v_v_440_){
_start:
{
uint8_t v_v_boxed_441_; lean_object* v_res_442_; 
v_v_boxed_441_ = lean_unbox(v_v_440_);
v_res_442_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_o_438_, v_k_439_, v_v_boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(lean_object* v_opts_443_, lean_object* v_opt_444_, uint8_t v_val_445_){
_start:
{
lean_object* v_name_446_; lean_object* v___x_447_; 
v_name_446_ = lean_ctor_get(v_opt_444_, 0);
lean_inc(v_name_446_);
lean_dec_ref(v_opt_444_);
v___x_447_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8(v_opts_443_, v_name_446_, v_val_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_opts_448_, lean_object* v_opt_449_, lean_object* v_val_450_){
_start:
{
uint8_t v_val_boxed_451_; lean_object* v_res_452_; 
v_val_boxed_451_ = lean_unbox(v_val_450_);
v_res_452_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_opts_448_, v_opt_449_, v_val_boxed_451_);
return v_res_452_;
}
}
static double _init_l_Lean_Compiler_compile___lam__1___closed__0(void){
_start:
{
lean_object* v___x_453_; double v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1000000000u);
v___x_454_ = lean_float_of_nat(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__4_spec__7___closed__0);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__1___closed__2(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__1, &l_Lean_Compiler_compile___lam__1___closed__1_once, _init_l_Lean_Compiler_compile___lam__1___closed__1);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* v___x_459_, uint8_t v___x_460_, lean_object* v___x_461_, lean_object* v___f_462_, lean_object* v_declNames_463_, lean_object* v___x_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v_a_475_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v_a_491_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; uint16_t v___y_549_; lean_object* v___y_550_; lean_object* v_fileName_551_; lean_object* v_fileMap_552_; lean_object* v_currNamespace_553_; lean_object* v_openDecls_554_; lean_object* v_initHeartbeats_555_; lean_object* v_maxHeartbeats_556_; lean_object* v_quotContext_557_; lean_object* v_currMacroScope_558_; lean_object* v_cancelTk_x3f_559_; lean_object* v_inheritedTraceOptions_560_; lean_object* v_currRecDepth_561_; lean_object* v_ref_562_; uint8_t v_suppressElabErrors_563_; uint8_t v_checkDeprecated_564_; uint8_t v_isRecordingDeps_565_; lean_object* v___y_566_; lean_object* v_toCold_579_; lean_object* v_currRecDepth_580_; lean_object* v_ref_581_; uint8_t v_suppressElabErrors_582_; uint8_t v_checkDeprecated_583_; uint8_t v_isRecordingDeps_584_; lean_object* v_fileName_585_; lean_object* v_fileMap_586_; lean_object* v_options_587_; lean_object* v_currNamespace_588_; lean_object* v_openDecls_589_; lean_object* v_initHeartbeats_590_; lean_object* v_maxHeartbeats_591_; lean_object* v_quotContext_592_; lean_object* v_currMacroScope_593_; lean_object* v_cancelTk_x3f_594_; lean_object* v_inheritedTraceOptions_595_; uint8_t v___y_597_; uint16_t v___y_598_; lean_object* v___y_599_; lean_object* v___y_622_; 
v_toCold_579_ = lean_ctor_get(v___y_465_, 0);
lean_inc_ref(v_toCold_579_);
v_currRecDepth_580_ = lean_ctor_get(v___y_465_, 1);
lean_inc(v_currRecDepth_580_);
v_ref_581_ = lean_ctor_get(v___y_465_, 2);
lean_inc(v_ref_581_);
v_suppressElabErrors_582_ = lean_ctor_get_uint8(v___y_465_, sizeof(void*)*3 + 2);
v_checkDeprecated_583_ = lean_ctor_get_uint8(v___y_465_, sizeof(void*)*3 + 3);
v_isRecordingDeps_584_ = lean_ctor_get_uint8(v___y_465_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_465_);
v_fileName_585_ = lean_ctor_get(v_toCold_579_, 0);
lean_inc_ref(v_fileName_585_);
v_fileMap_586_ = lean_ctor_get(v_toCold_579_, 1);
lean_inc_ref(v_fileMap_586_);
v_options_587_ = lean_ctor_get(v_toCold_579_, 2);
lean_inc_ref(v_options_587_);
v_currNamespace_588_ = lean_ctor_get(v_toCold_579_, 4);
lean_inc(v_currNamespace_588_);
v_openDecls_589_ = lean_ctor_get(v_toCold_579_, 5);
lean_inc(v_openDecls_589_);
v_initHeartbeats_590_ = lean_ctor_get(v_toCold_579_, 6);
lean_inc(v_initHeartbeats_590_);
v_maxHeartbeats_591_ = lean_ctor_get(v_toCold_579_, 7);
lean_inc(v_maxHeartbeats_591_);
v_quotContext_592_ = lean_ctor_get(v_toCold_579_, 8);
lean_inc(v_quotContext_592_);
v_currMacroScope_593_ = lean_ctor_get(v_toCold_579_, 9);
lean_inc(v_currMacroScope_593_);
v_cancelTk_x3f_594_ = lean_ctor_get(v_toCold_579_, 10);
lean_inc(v_cancelTk_x3f_594_);
v_inheritedTraceOptions_595_ = lean_ctor_get(v_toCold_579_, 11);
lean_inc_ref(v_inheritedTraceOptions_595_);
lean_dec_ref(v_toCold_579_);
if (v_isRecordingDeps_584_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_633_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__5(v_options_587_, v___x_632_, v_isRecordingDeps_584_);
v___y_622_ = v___x_633_;
goto v___jp_621_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_587_);
v___y_622_ = v___x_634_;
goto v___jp_621_;
}
v___jp_468_:
{
lean_object* v___x_476_; double v___x_477_; double v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_476_ = lean_io_get_num_heartbeats();
v___x_477_ = lean_float_of_nat(v___y_473_);
v___x_478_ = lean_float_of_nat(v___x_476_);
v___x_479_ = lean_box_float(v___x_477_);
v___x_480_ = lean_box_float(v___x_478_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_a_475_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_459_, v___x_460_, v___x_461_, v___y_470_, v___y_474_, v___y_472_, v___f_462_, v___x_482_, v___y_469_, v___y_471_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v___y_470_);
return v___x_483_;
}
v___jp_484_:
{
lean_object* v___x_492_; double v___x_493_; double v___x_494_; double v___x_495_; double v___x_496_; double v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_492_ = lean_io_mono_nanos_now();
v___x_493_ = lean_float_of_nat(v___y_490_);
v___x_494_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_495_ = lean_float_div(v___x_493_, v___x_494_);
v___x_496_ = lean_float_of_nat(v___x_492_);
v___x_497_ = lean_float_div(v___x_496_, v___x_494_);
v___x_498_ = lean_box_float(v___x_495_);
v___x_499_ = lean_box_float(v___x_497_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_a_491_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4(v___x_459_, v___x_460_, v___x_461_, v___y_486_, v___y_489_, v___y_488_, v___f_462_, v___x_501_, v___y_485_, v___y_487_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_486_);
return v___x_502_;
}
v___jp_503_:
{
lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__2___redArg(v___y_506_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l_Lean_trace_profiler_useHeartbeats;
v___x_511_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_505_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_io_mono_nanos_now();
v___x_513_ = l_Lean_Compiler_LCNF_main(v_declNames_463_, v___x_464_, v___y_504_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
v___y_485_ = v___y_504_;
v___y_486_ = v___y_505_;
v___y_487_ = v___y_506_;
v___y_488_ = v_a_509_;
v___y_489_ = v___y_507_;
v___y_490_ = v___x_512_;
v_a_491_ = v___x_519_;
goto v___jp_484_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v___y_485_ = v___y_504_;
v___y_486_ = v___y_505_;
v___y_487_ = v___y_506_;
v___y_488_ = v_a_509_;
v___y_489_ = v___y_507_;
v___y_490_ = v___x_512_;
v_a_491_ = v___x_527_;
goto v___jp_484_;
}
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_io_get_num_heartbeats();
v___x_531_ = l_Lean_Compiler_LCNF_main(v_declNames_463_, v___x_464_, v___y_504_, v___y_506_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 1);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v___y_469_ = v___y_504_;
v___y_470_ = v___y_505_;
v___y_471_ = v___y_506_;
v___y_472_ = v_a_509_;
v___y_473_ = v___x_530_;
v___y_474_ = v___y_507_;
v_a_475_ = v___x_537_;
goto v___jp_468_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_531_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_531_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_469_ = v___y_504_;
v___y_470_ = v___y_505_;
v___y_471_ = v___y_506_;
v___y_472_ = v_a_509_;
v___y_473_ = v___x_530_;
v___y_474_ = v___y_507_;
v_a_475_ = v___x_545_;
goto v___jp_468_;
}
}
}
}
}
v___jp_548_:
{
uint8_t v_hasTrace_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_hasTrace_567_ = lean_ctor_get_uint8(v___y_550_, sizeof(void*)*1);
v___x_568_ = l_Lean_maxRecDepth;
v___x_569_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__1(v___y_550_, v___x_568_);
lean_inc_ref(v_inheritedTraceOptions_560_);
lean_inc_ref(v___y_550_);
v___x_570_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_570_, 0, v_fileName_551_);
lean_ctor_set(v___x_570_, 1, v_fileMap_552_);
lean_ctor_set(v___x_570_, 2, v___y_550_);
lean_ctor_set(v___x_570_, 3, v___x_569_);
lean_ctor_set(v___x_570_, 4, v_currNamespace_553_);
lean_ctor_set(v___x_570_, 5, v_openDecls_554_);
lean_ctor_set(v___x_570_, 6, v_initHeartbeats_555_);
lean_ctor_set(v___x_570_, 7, v_maxHeartbeats_556_);
lean_ctor_set(v___x_570_, 8, v_quotContext_557_);
lean_ctor_set(v___x_570_, 9, v_currMacroScope_558_);
lean_ctor_set(v___x_570_, 10, v_cancelTk_x3f_559_);
lean_ctor_set(v___x_570_, 11, v_inheritedTraceOptions_560_);
v___x_571_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_currRecDepth_561_);
lean_ctor_set(v___x_571_, 2, v_ref_562_);
lean_ctor_set_uint16(v___x_571_, sizeof(void*)*3, v___y_549_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3 + 2, v_suppressElabErrors_563_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3 + 3, v_checkDeprecated_564_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3 + 4, v_isRecordingDeps_565_);
if (v_hasTrace_567_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v_inheritedTraceOptions_560_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v___f_462_);
lean_dec_ref(v___x_461_);
lean_dec(v___x_459_);
v___x_572_ = l_Lean_Compiler_LCNF_main(v_declNames_463_, v___x_464_, v___x_571_, v___y_566_);
lean_dec_ref_known(v___x_571_, 3);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__5_spec__8___closed__1));
lean_inc(v___x_459_);
v___x_574_ = l_Lean_Name_append(v___x_573_, v___x_459_);
v___x_575_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_560_, v___y_550_, v___x_574_);
lean_dec(v___x_574_);
lean_dec_ref(v_inheritedTraceOptions_560_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = l_Lean_trace_profiler;
v___x_577_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v___y_550_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec_ref(v___y_550_);
lean_dec_ref(v___f_462_);
lean_dec_ref(v___x_461_);
lean_dec(v___x_459_);
v___x_578_ = l_Lean_Compiler_LCNF_main(v_declNames_463_, v___x_464_, v___x_571_, v___y_566_);
lean_dec_ref_known(v___x_571_, 3);
return v___x_578_;
}
else
{
v___y_504_ = v___x_571_;
v___y_505_ = v___y_550_;
v___y_506_ = v___y_566_;
v___y_507_ = v___x_575_;
goto v___jp_503_;
}
}
else
{
v___y_504_ = v___x_571_;
v___y_505_ = v___y_550_;
v___y_506_ = v___y_566_;
v___y_507_ = v___x_575_;
goto v___jp_503_;
}
}
}
v___jp_596_:
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_traceState_605_; lean_object* v_recordedDeps_606_; lean_object* v_messages_607_; lean_object* v_infoState_608_; lean_object* v_snapshotTasks_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_619_; 
v___x_600_ = lean_st_ref_take(v___y_466_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_600_, 1);
v_ngen_603_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_600_, 3);
v_traceState_605_ = lean_ctor_get(v___x_600_, 4);
v_recordedDeps_606_ = lean_ctor_get(v___x_600_, 6);
v_messages_607_ = lean_ctor_get(v___x_600_, 7);
v_infoState_608_ = lean_ctor_get(v___x_600_, 8);
v_snapshotTasks_609_ = lean_ctor_get(v___x_600_, 9);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_600_, 5);
lean_dec(v_unused_620_);
v___x_611_ = v___x_600_;
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snapshotTasks_609_);
lean_inc(v_infoState_608_);
lean_inc(v_messages_607_);
lean_inc(v_recordedDeps_606_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_613_ = l_Lean_Kernel_enableDiag(v_env_601_, v___y_597_);
v___x_614_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 5, v___x_614_);
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_traceState_605_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_recordedDeps_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_messages_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_infoState_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_snapshotTasks_609_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = lean_st_ref_put(v___y_466_, v___x_616_);
v___y_549_ = v___y_598_;
v___y_550_ = v___y_599_;
v_fileName_551_ = v_fileName_585_;
v_fileMap_552_ = v_fileMap_586_;
v_currNamespace_553_ = v_currNamespace_588_;
v_openDecls_554_ = v_openDecls_589_;
v_initHeartbeats_555_ = v_initHeartbeats_590_;
v_maxHeartbeats_556_ = v_maxHeartbeats_591_;
v_quotContext_557_ = v_quotContext_592_;
v_currMacroScope_558_ = v_currMacroScope_593_;
v_cancelTk_x3f_559_ = v_cancelTk_x3f_594_;
v_inheritedTraceOptions_560_ = v_inheritedTraceOptions_595_;
v_currRecDepth_561_ = v_currRecDepth_580_;
v_ref_562_ = v_ref_581_;
v_suppressElabErrors_563_ = v_suppressElabErrors_582_;
v_checkDeprecated_564_ = v_checkDeprecated_583_;
v_isRecordingDeps_565_ = v_isRecordingDeps_584_;
v___y_566_ = v___y_466_;
goto v___jp_548_;
}
}
}
v___jp_621_:
{
uint16_t v___x_623_; lean_object* v___x_624_; lean_object* v_env_625_; uint8_t v___x_626_; uint16_t v___x_627_; uint16_t v___x_628_; uint16_t v___x_629_; uint8_t v___x_630_; 
v___x_623_ = l_Lean_OptionFlags_ofOptions(v___y_622_);
v___x_624_ = lean_st_ref_get(v___y_466_);
v_env_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_ref(v_env_625_);
lean_dec(v___x_624_);
v___x_626_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_625_);
lean_dec_ref(v_env_625_);
v___x_627_ = 512;
v___x_628_ = lean_uint16_land(v___x_623_, v___x_627_);
v___x_629_ = 0;
v___x_630_ = lean_uint16_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
if (v___x_626_ == 0)
{
v___y_597_ = v___x_460_;
v___y_598_ = v___x_623_;
v___y_599_ = v___y_622_;
goto v___jp_596_;
}
else
{
v___y_549_ = v___x_623_;
v___y_550_ = v___y_622_;
v_fileName_551_ = v_fileName_585_;
v_fileMap_552_ = v_fileMap_586_;
v_currNamespace_553_ = v_currNamespace_588_;
v_openDecls_554_ = v_openDecls_589_;
v_initHeartbeats_555_ = v_initHeartbeats_590_;
v_maxHeartbeats_556_ = v_maxHeartbeats_591_;
v_quotContext_557_ = v_quotContext_592_;
v_currMacroScope_558_ = v_currMacroScope_593_;
v_cancelTk_x3f_559_ = v_cancelTk_x3f_594_;
v_inheritedTraceOptions_560_ = v_inheritedTraceOptions_595_;
v_currRecDepth_561_ = v_currRecDepth_580_;
v_ref_562_ = v_ref_581_;
v_suppressElabErrors_563_ = v_suppressElabErrors_582_;
v_checkDeprecated_564_ = v_checkDeprecated_583_;
v_isRecordingDeps_565_ = v_isRecordingDeps_584_;
v___y_566_ = v___y_466_;
goto v___jp_548_;
}
}
else
{
if (v___x_626_ == 0)
{
v___y_549_ = v___x_623_;
v___y_550_ = v___y_622_;
v_fileName_551_ = v_fileName_585_;
v_fileMap_552_ = v_fileMap_586_;
v_currNamespace_553_ = v_currNamespace_588_;
v_openDecls_554_ = v_openDecls_589_;
v_initHeartbeats_555_ = v_initHeartbeats_590_;
v_maxHeartbeats_556_ = v_maxHeartbeats_591_;
v_quotContext_557_ = v_quotContext_592_;
v_currMacroScope_558_ = v_currMacroScope_593_;
v_cancelTk_x3f_559_ = v_cancelTk_x3f_594_;
v_inheritedTraceOptions_560_ = v_inheritedTraceOptions_595_;
v_currRecDepth_561_ = v_currRecDepth_580_;
v_ref_562_ = v_ref_581_;
v_suppressElabErrors_563_ = v_suppressElabErrors_582_;
v_checkDeprecated_564_ = v_checkDeprecated_583_;
v_isRecordingDeps_565_ = v_isRecordingDeps_584_;
v___y_566_ = v___y_466_;
goto v___jp_548_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = 0;
v___y_597_ = v___x_631_;
v___y_598_ = v___x_623_;
v___y_599_ = v___y_622_;
goto v___jp_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v___f_638_, lean_object* v_declNames_639_, lean_object* v___x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
uint8_t v___x_7145__boxed_644_; lean_object* v_res_645_; 
v___x_7145__boxed_644_ = lean_unbox(v___x_636_);
v_res_645_ = l_Lean_Compiler_compile___lam__1(v___x_635_, v___x_7145__boxed_644_, v___x_637_, v___f_638_, v_declNames_639_, v___x_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* v_declNames_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc_ref(v_declNames_651_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(v___f_655_, 0, v_declNames_651_);
v___x_656_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_652_);
v___x_657_ = ((lean_object*)(l_Lean_Compiler_compile___closed__0));
v___x_658_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_659_ = l_Lean_Options_empty;
v___x_660_ = 1;
v___x_661_ = ((lean_object*)(l_Lean_Compiler_compile___closed__3));
v___x_662_ = lean_box(v___x_660_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1___boxed), 9, 6);
lean_closure_set(v___f_663_, 0, v___x_658_);
lean_closure_set(v___f_663_, 1, v___x_662_);
lean_closure_set(v___f_663_, 2, v___x_661_);
lean_closure_set(v___f_663_, 3, v___f_655_);
lean_closure_set(v___f_663_, 4, v_declNames_651_);
lean_closure_set(v___f_663_, 5, v___x_659_);
v___x_664_ = lean_box(0);
v___x_665_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(v___x_657_, v___x_656_, v___f_663_, v___x_664_, v_a_652_, v_a_653_);
lean_dec_ref(v___x_656_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___boxed(lean_object* v_declNames_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Compiler_compile(v_declNames_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(lean_object* v_00_u03b1_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___redArg(v_x_672_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5___boxed(lean_object* v_00_u03b1_677_, lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__4_spec__5(v_00_u03b1_677_, v_x_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = ((lean_object*)(l_Lean_Compiler_compile___closed__2));
v___x_744_ = 0;
v___x_745_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_746_ = l_Lean_registerTraceClass(v___x_743_, v___x_744_, v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_747_ = ((lean_object*)(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_));
v___x_748_ = l_Lean_registerTraceClass(v___x_747_, v___x_744_, v___x_745_);
return v___x_748_;
}
else
{
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
return v_res_750_;
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

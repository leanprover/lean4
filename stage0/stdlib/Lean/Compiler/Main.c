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
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_15_ = ((size_t)5ULL);
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_unsigned_to_nat(32u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__0);
v___x_20_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_16_);
lean_ctor_set(v___x_20_, 3, v___x_16_);
lean_ctor_set_usize(v___x_20_, 4, v___x_15_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg(lean_object* v___y_21_){
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
v___x_44_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg___boxed(lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg(v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3(lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg(v___y_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___boxed(lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3(v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(lean_object* v_opts_67_, lean_object* v_opt_68_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4___boxed(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(v_opts_77_, v_opt_78_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(size_t v_sz_188_, size_t v_i_189_, lean_object* v_bs_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_lt(v_i_189_, v_sz_188_);
if (v___x_191_ == 0)
{
return v_bs_190_;
}
else
{
lean_object* v_v_192_; lean_object* v_msg_193_; lean_object* v___x_194_; lean_object* v_bs_x27_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v_v_192_ = lean_array_uget_borrowed(v_bs_190_, v_i_189_);
v_msg_193_ = lean_ctor_get(v_v_192_, 1);
lean_inc_ref(v_msg_193_);
v___x_194_ = lean_unsigned_to_nat(0u);
v_bs_x27_195_ = lean_array_uset(v_bs_190_, v_i_189_, v___x_194_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_189_, v___x_196_);
v___x_198_ = lean_array_uset(v_bs_x27_195_, v_i_189_, v_msg_193_);
v_i_189_ = v___x_197_;
v_bs_190_ = v___x_198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8___boxed(lean_object* v_sz_200_, lean_object* v_i_201_, lean_object* v_bs_202_){
_start:
{
size_t v_sz_boxed_203_; size_t v_i_boxed_204_; lean_object* v_res_205_; 
v_sz_boxed_203_ = lean_unbox_usize(v_sz_200_);
lean_dec(v_sz_200_);
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(v_sz_boxed_203_, v_i_boxed_204_, v_bs_202_);
return v_res_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_206_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_alloc_ctor(0, 11, 0);
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
return v___x_211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4(void){
_start:
{
size_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = ((size_t)5ULL);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_unsigned_to_nat(32u);
v___x_218_ = lean_mk_empty_array_with_capacity(v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__3);
v___x_220_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_216_);
lean_ctor_set(v___x_220_, 3, v___x_216_);
lean_ctor_set_usize(v___x_220_, 4, v___x_215_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_box(1);
v___x_222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__4);
v___x_223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__1);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_221_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_toCold_230_; lean_object* v_env_231_; lean_object* v_options_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_229_ = lean_st_ref_get(v___y_227_);
v_toCold_230_ = lean_ctor_get(v___y_226_, 0);
v_env_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_env_231_);
lean_dec(v___x_229_);
v_options_232_ = lean_ctor_get(v_toCold_230_, 2);
v___x_233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__2);
v___x_234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__5);
lean_inc_ref(v_options_232_);
v___x_235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_235_, 0, v_env_231_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
lean_ctor_set(v___x_235_, 3, v_options_232_);
v___x_236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_msgData_225_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(v_msgData_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(lean_object* v_oldTraces_243_, lean_object* v_data_244_, lean_object* v_ref_245_, lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_toCold_250_; lean_object* v_currRecDepth_251_; lean_object* v_ref_252_; uint16_t v_optionFlags_253_; uint8_t v_suppressElabErrors_254_; uint8_t v_isRecordingDeps_255_; lean_object* v_ref_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_traceState_259_; lean_object* v_traces_260_; lean_object* v___x_261_; size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v_msg_265_; lean_object* v___x_266_; lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_305_; 
v_toCold_250_ = lean_ctor_get(v___y_247_, 0);
v_currRecDepth_251_ = lean_ctor_get(v___y_247_, 1);
v_ref_252_ = lean_ctor_get(v___y_247_, 2);
v_optionFlags_253_ = lean_ctor_get_uint16(v___y_247_, sizeof(void*)*3);
v_suppressElabErrors_254_ = lean_ctor_get_uint8(v___y_247_, sizeof(void*)*3 + 2);
v_isRecordingDeps_255_ = lean_ctor_get_uint8(v___y_247_, sizeof(void*)*3 + 3);
v_ref_256_ = l_Lean_replaceRef(v_ref_245_, v_ref_252_);
lean_inc(v_currRecDepth_251_);
lean_inc_ref(v_toCold_250_);
v___x_257_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_257_, 0, v_toCold_250_);
lean_ctor_set(v___x_257_, 1, v_currRecDepth_251_);
lean_ctor_set(v___x_257_, 2, v_ref_256_);
lean_ctor_set_uint16(v___x_257_, sizeof(void*)*3, v_optionFlags_253_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*3 + 2, v_suppressElabErrors_254_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*3 + 3, v_isRecordingDeps_255_);
v___x_258_ = lean_st_ref_get(v___y_248_);
v_traceState_259_ = lean_ctor_get(v___x_258_, 4);
lean_inc_ref(v_traceState_259_);
lean_dec(v___x_258_);
v_traces_260_ = lean_ctor_get(v_traceState_259_, 0);
lean_inc_ref(v_traces_260_);
lean_dec_ref(v_traceState_259_);
v___x_261_ = l_Lean_PersistentArray_toArray___redArg(v_traces_260_);
lean_dec_ref(v_traces_260_);
v_sz_262_ = lean_array_size(v___x_261_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__8(v_sz_262_, v___x_263_, v___x_261_);
v_msg_265_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_265_, 0, v_data_244_);
lean_ctor_set(v_msg_265_, 1, v_msg_246_);
lean_ctor_set(v_msg_265_, 2, v___x_264_);
v___x_266_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9(v_msg_265_, v___x_257_, v___y_248_);
lean_dec_ref_known(v___x_257_, 3);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_305_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_305_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_305_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v_traceState_272_; lean_object* v_env_273_; lean_object* v_nextMacroScope_274_; lean_object* v_ngen_275_; lean_object* v_auxDeclNGen_276_; lean_object* v_cache_277_; lean_object* v_recordedDeps_278_; lean_object* v_messages_279_; lean_object* v_infoState_280_; lean_object* v_snapshotTasks_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_304_; 
v___x_271_ = lean_st_ref_take(v___y_248_);
v_traceState_272_ = lean_ctor_get(v___x_271_, 4);
v_env_273_ = lean_ctor_get(v___x_271_, 0);
v_nextMacroScope_274_ = lean_ctor_get(v___x_271_, 1);
v_ngen_275_ = lean_ctor_get(v___x_271_, 2);
v_auxDeclNGen_276_ = lean_ctor_get(v___x_271_, 3);
v_cache_277_ = lean_ctor_get(v___x_271_, 5);
v_recordedDeps_278_ = lean_ctor_get(v___x_271_, 6);
v_messages_279_ = lean_ctor_get(v___x_271_, 7);
v_infoState_280_ = lean_ctor_get(v___x_271_, 8);
v_snapshotTasks_281_ = lean_ctor_get(v___x_271_, 9);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_304_ == 0)
{
v___x_283_ = v___x_271_;
v_isShared_284_ = v_isSharedCheck_304_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_snapshotTasks_281_);
lean_inc(v_infoState_280_);
lean_inc(v_messages_279_);
lean_inc(v_recordedDeps_278_);
lean_inc(v_cache_277_);
lean_inc(v_traceState_272_);
lean_inc(v_auxDeclNGen_276_);
lean_inc(v_ngen_275_);
lean_inc(v_nextMacroScope_274_);
lean_inc(v_env_273_);
lean_dec(v___x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_304_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint64_t v_tid_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_302_; 
v_tid_285_ = lean_ctor_get_uint64(v_traceState_272_, sizeof(void*)*1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_traceState_272_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_traceState_272_, 0);
lean_dec(v_unused_303_);
v___x_287_ = v_traceState_272_;
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_traceState_272_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_ref_245_);
lean_ctor_set(v___x_290_, 1, v_a_267_);
v___x_291_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_243_, v___x_290_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_291_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_291_);
lean_ctor_set_uint64(v_reuseFailAlloc_301_, sizeof(void*)*1, v_tid_285_);
v___x_293_ = v_reuseFailAlloc_301_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 4, v___x_293_);
v___x_295_ = v___x_283_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_env_273_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_nextMacroScope_274_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_ngen_275_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_auxDeclNGen_276_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 5, v_cache_277_);
lean_ctor_set(v_reuseFailAlloc_300_, 6, v_recordedDeps_278_);
lean_ctor_set(v_reuseFailAlloc_300_, 7, v_messages_279_);
lean_ctor_set(v_reuseFailAlloc_300_, 8, v_infoState_280_);
lean_ctor_set(v_reuseFailAlloc_300_, 9, v_snapshotTasks_281_);
v___x_295_ = v_reuseFailAlloc_300_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_st_ref_put(v___y_248_, v___x_295_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_289_);
v___x_298_ = v___x_269_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_289_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(lean_object* v_oldTraces_306_, lean_object* v_data_307_, lean_object* v_ref_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_oldTraces_306_, v_data_307_, v_ref_308_, v_msg_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(lean_object* v_e_314_){
_start:
{
if (lean_obj_tag(v_e_314_) == 0)
{
uint8_t v___x_315_; 
v___x_315_ = 2;
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(lean_object* v_e_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_e_317_);
lean_dec_ref(v_e_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v_x_320_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v_x_320_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v_x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v_x_320_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v_x_320_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v_x_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 0);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg___boxed(lean_object* v_x_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_x_338_);
return v_res_340_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0(void){
_start:
{
lean_object* v___x_341_; double v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_float_of_nat(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3(void){
_start:
{
lean_object* v___x_346_; double v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1000u);
v___x_347_ = lean_float_of_nat(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(lean_object* v_cls_348_, uint8_t v_collapsed_349_, lean_object* v_tag_350_, lean_object* v_opts_351_, uint8_t v_clsEnabled_352_, lean_object* v_oldTraces_353_, lean_object* v_msg_354_, lean_object* v_resStartStop_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_fst_359_; lean_object* v_snd_360_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_data_364_; lean_object* v_fst_367_; lean_object* v_snd_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___y_372_; lean_object* v_a_373_; uint8_t v___y_388_; double v___y_420_; 
v_fst_359_ = lean_ctor_get(v_resStartStop_355_, 0);
lean_inc(v_fst_359_);
v_snd_360_ = lean_ctor_get(v_resStartStop_355_, 1);
lean_inc(v_snd_360_);
lean_dec_ref(v_resStartStop_355_);
v_fst_367_ = lean_ctor_get(v_snd_360_, 0);
lean_inc(v_fst_367_);
v_snd_368_ = lean_ctor_get(v_snd_360_, 1);
lean_inc(v_snd_368_);
lean_dec(v_snd_360_);
v___x_369_ = l_Lean_trace_profiler;
v___x_370_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(v_opts_351_, v___x_369_);
if (v___x_370_ == 0)
{
v___y_388_ = v___x_370_;
goto v___jp_387_;
}
else
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Lean_trace_profiler_useHeartbeats;
v___x_426_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(v_opts_351_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; double v___x_429_; double v___x_430_; double v___x_431_; 
v___x_427_ = l_Lean_trace_profiler_threshold;
v___x_428_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_351_, v___x_427_);
v___x_429_ = lean_float_of_nat(v___x_428_);
v___x_430_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3);
v___x_431_ = lean_float_div(v___x_429_, v___x_430_);
v___y_420_ = v___x_431_;
goto v___jp_419_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; double v___x_434_; 
v___x_432_ = l_Lean_trace_profiler_threshold;
v___x_433_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_351_, v___x_432_);
v___x_434_ = lean_float_of_nat(v___x_433_);
v___y_420_ = v___x_434_;
goto v___jp_419_;
}
}
v___jp_361_:
{
lean_object* v___x_365_; 
lean_inc(v___y_362_);
v___x_365_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_oldTraces_353_, v_data_364_, v___y_362_, v___y_363_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_366_; 
lean_dec_ref_known(v___x_365_, 1);
v___x_366_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_fst_359_);
return v___x_366_;
}
else
{
lean_dec(v_fst_359_);
return v___x_365_;
}
}
v___jp_371_:
{
uint8_t v_result_374_; lean_object* v___x_375_; lean_object* v___x_376_; double v___x_377_; lean_object* v_data_378_; 
v_result_374_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_fst_359_);
v___x_375_ = lean_box(v_result_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___x_377_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0);
lean_inc_ref(v_tag_350_);
lean_inc_ref(v___x_376_);
lean_inc(v_cls_348_);
v_data_378_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_378_, 0, v_cls_348_);
lean_ctor_set(v_data_378_, 1, v___x_376_);
lean_ctor_set(v_data_378_, 2, v_tag_350_);
lean_ctor_set_float(v_data_378_, sizeof(void*)*3, v___x_377_);
lean_ctor_set_float(v_data_378_, sizeof(void*)*3 + 8, v___x_377_);
lean_ctor_set_uint8(v_data_378_, sizeof(void*)*3 + 16, v_collapsed_349_);
if (v___x_370_ == 0)
{
lean_dec_ref_known(v___x_376_, 1);
lean_dec(v_snd_368_);
lean_dec(v_fst_367_);
lean_dec_ref(v_tag_350_);
lean_dec(v_cls_348_);
v___y_362_ = v___y_372_;
v___y_363_ = v_a_373_;
v_data_364_ = v_data_378_;
goto v___jp_361_;
}
else
{
lean_object* v_data_379_; double v___x_380_; double v___x_381_; 
lean_dec_ref_known(v_data_378_, 3);
v_data_379_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_379_, 0, v_cls_348_);
lean_ctor_set(v_data_379_, 1, v___x_376_);
lean_ctor_set(v_data_379_, 2, v_tag_350_);
v___x_380_ = lean_unbox_float(v_fst_367_);
lean_dec(v_fst_367_);
lean_ctor_set_float(v_data_379_, sizeof(void*)*3, v___x_380_);
v___x_381_ = lean_unbox_float(v_snd_368_);
lean_dec(v_snd_368_);
lean_ctor_set_float(v_data_379_, sizeof(void*)*3 + 8, v___x_381_);
lean_ctor_set_uint8(v_data_379_, sizeof(void*)*3 + 16, v_collapsed_349_);
v___y_362_ = v___y_372_;
v___y_363_ = v_a_373_;
v_data_364_ = v_data_379_;
goto v___jp_361_;
}
}
v___jp_382_:
{
lean_object* v_ref_383_; lean_object* v___x_384_; 
v_ref_383_ = lean_ctor_get(v___y_356_, 2);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v_fst_359_);
v___x_384_ = lean_apply_4(v_msg_354_, v_fst_359_, v___y_356_, v___y_357_, lean_box(0));
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___y_372_ = v_ref_383_;
v_a_373_ = v_a_385_;
goto v___jp_371_;
}
else
{
lean_object* v___x_386_; 
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2);
v___y_372_ = v_ref_383_;
v_a_373_ = v___x_386_;
goto v___jp_371_;
}
}
v___jp_387_:
{
if (v_clsEnabled_352_ == 0)
{
if (v___y_388_ == 0)
{
lean_object* v___x_389_; lean_object* v_traceState_390_; lean_object* v_env_391_; lean_object* v_nextMacroScope_392_; lean_object* v_ngen_393_; lean_object* v_auxDeclNGen_394_; lean_object* v_cache_395_; lean_object* v_recordedDeps_396_; lean_object* v_messages_397_; lean_object* v_infoState_398_; lean_object* v_snapshotTasks_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_snd_368_);
lean_dec(v_fst_367_);
lean_dec_ref(v_msg_354_);
lean_dec_ref(v_tag_350_);
lean_dec(v_cls_348_);
v___x_389_ = lean_st_ref_take(v___y_357_);
v_traceState_390_ = lean_ctor_get(v___x_389_, 4);
v_env_391_ = lean_ctor_get(v___x_389_, 0);
v_nextMacroScope_392_ = lean_ctor_get(v___x_389_, 1);
v_ngen_393_ = lean_ctor_get(v___x_389_, 2);
v_auxDeclNGen_394_ = lean_ctor_get(v___x_389_, 3);
v_cache_395_ = lean_ctor_get(v___x_389_, 5);
v_recordedDeps_396_ = lean_ctor_get(v___x_389_, 6);
v_messages_397_ = lean_ctor_get(v___x_389_, 7);
v_infoState_398_ = lean_ctor_get(v___x_389_, 8);
v_snapshotTasks_399_ = lean_ctor_get(v___x_389_, 9);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_418_ == 0)
{
v___x_401_ = v___x_389_;
v_isShared_402_ = v_isSharedCheck_418_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_snapshotTasks_399_);
lean_inc(v_infoState_398_);
lean_inc(v_messages_397_);
lean_inc(v_recordedDeps_396_);
lean_inc(v_cache_395_);
lean_inc(v_traceState_390_);
lean_inc(v_auxDeclNGen_394_);
lean_inc(v_ngen_393_);
lean_inc(v_nextMacroScope_392_);
lean_inc(v_env_391_);
lean_dec(v___x_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_418_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint64_t v_tid_403_; lean_object* v_traces_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_417_; 
v_tid_403_ = lean_ctor_get_uint64(v_traceState_390_, sizeof(void*)*1);
v_traces_404_ = lean_ctor_get(v_traceState_390_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_traceState_390_);
if (v_isSharedCheck_417_ == 0)
{
v___x_406_ = v_traceState_390_;
v_isShared_407_ = v_isSharedCheck_417_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_traces_404_);
lean_dec(v_traceState_390_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_417_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_353_, v_traces_404_);
lean_dec_ref(v_traces_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_408_);
lean_ctor_set_uint64(v_reuseFailAlloc_416_, sizeof(void*)*1, v_tid_403_);
v___x_410_ = v_reuseFailAlloc_416_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 4, v___x_410_);
v___x_412_ = v___x_401_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_env_391_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_nextMacroScope_392_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_ngen_393_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_auxDeclNGen_394_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_415_, 5, v_cache_395_);
lean_ctor_set(v_reuseFailAlloc_415_, 6, v_recordedDeps_396_);
lean_ctor_set(v_reuseFailAlloc_415_, 7, v_messages_397_);
lean_ctor_set(v_reuseFailAlloc_415_, 8, v_infoState_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 9, v_snapshotTasks_399_);
v___x_412_ = v_reuseFailAlloc_415_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_st_ref_put(v___y_357_, v___x_412_);
v___x_414_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_fst_359_);
return v___x_414_;
}
}
}
}
}
else
{
goto v___jp_382_;
}
}
else
{
goto v___jp_382_;
}
}
v___jp_419_:
{
double v___x_421_; double v___x_422_; double v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_unbox_float(v_snd_368_);
v___x_422_ = lean_unbox_float(v_fst_367_);
v___x_423_ = lean_float_sub(v___x_421_, v___x_422_);
v___x_424_ = lean_float_decLt(v___y_420_, v___x_423_);
v___y_388_ = v___x_424_;
goto v___jp_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(lean_object* v_cls_435_, lean_object* v_collapsed_436_, lean_object* v_tag_437_, lean_object* v_opts_438_, lean_object* v_clsEnabled_439_, lean_object* v_oldTraces_440_, lean_object* v_msg_441_, lean_object* v_resStartStop_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v_collapsed_boxed_446_; uint8_t v_clsEnabled_boxed_447_; lean_object* v_res_448_; 
v_collapsed_boxed_446_ = lean_unbox(v_collapsed_436_);
v_clsEnabled_boxed_447_ = lean_unbox(v_clsEnabled_439_);
v_res_448_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v_cls_435_, v_collapsed_boxed_446_, v_tag_437_, v_opts_438_, v_clsEnabled_boxed_447_, v_oldTraces_440_, v_msg_441_, v_resStartStop_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_opts_438_);
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
v___x_451_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6_spec__9___closed__0);
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
lean_object* v_toCold_464_; lean_object* v_currRecDepth_465_; lean_object* v_ref_466_; uint8_t v_suppressElabErrors_467_; uint8_t v_isRecordingDeps_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_631_; 
v_toCold_464_ = lean_ctor_get(v___y_461_, 0);
v_currRecDepth_465_ = lean_ctor_get(v___y_461_, 1);
v_ref_466_ = lean_ctor_get(v___y_461_, 2);
v_suppressElabErrors_467_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*3 + 2);
v_isRecordingDeps_468_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*3 + 3);
v_isSharedCheck_631_ = !lean_is_exclusive(v___y_461_);
if (v_isSharedCheck_631_ == 0)
{
v___x_470_ = v___y_461_;
v_isShared_471_ = v_isSharedCheck_631_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_ref_466_);
lean_inc(v_currRecDepth_465_);
lean_inc(v_toCold_464_);
lean_dec(v___y_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_631_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_fileName_472_; lean_object* v_fileMap_473_; lean_object* v_options_474_; lean_object* v_currNamespace_475_; lean_object* v_openDecls_476_; lean_object* v_initHeartbeats_477_; lean_object* v_maxHeartbeats_478_; lean_object* v_quotContext_479_; lean_object* v_currMacroScope_480_; lean_object* v_cancelTk_x3f_481_; lean_object* v_inheritedTraceOptions_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_629_; 
v_fileName_472_ = lean_ctor_get(v_toCold_464_, 0);
v_fileMap_473_ = lean_ctor_get(v_toCold_464_, 1);
v_options_474_ = lean_ctor_get(v_toCold_464_, 2);
v_currNamespace_475_ = lean_ctor_get(v_toCold_464_, 4);
v_openDecls_476_ = lean_ctor_get(v_toCold_464_, 5);
v_initHeartbeats_477_ = lean_ctor_get(v_toCold_464_, 6);
v_maxHeartbeats_478_ = lean_ctor_get(v_toCold_464_, 7);
v_quotContext_479_ = lean_ctor_get(v_toCold_464_, 8);
v_currMacroScope_480_ = lean_ctor_get(v_toCold_464_, 9);
v_cancelTk_x3f_481_ = lean_ctor_get(v_toCold_464_, 10);
v_inheritedTraceOptions_482_ = lean_ctor_get(v_toCold_464_, 11);
v_isSharedCheck_629_ = !lean_is_exclusive(v_toCold_464_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_toCold_464_, 3);
lean_dec(v_unused_630_);
v___x_484_ = v_toCold_464_;
v_isShared_485_ = v_isSharedCheck_629_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_inheritedTraceOptions_482_);
lean_inc(v_cancelTk_x3f_481_);
lean_inc(v_currMacroScope_480_);
lean_inc(v_quotContext_479_);
lean_inc(v_maxHeartbeats_478_);
lean_inc(v_initHeartbeats_477_);
lean_inc(v_openDecls_476_);
lean_inc(v_currNamespace_475_);
lean_inc(v_options_474_);
lean_inc(v_fileMap_473_);
lean_inc(v_fileName_472_);
lean_dec(v_toCold_464_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_629_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_a_495_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v_a_510_; lean_object* v___y_523_; uint8_t v___y_524_; lean_object* v___y_525_; uint16_t v___x_566_; lean_object* v_fileName_568_; lean_object* v_fileMap_569_; lean_object* v_currNamespace_570_; lean_object* v_openDecls_571_; lean_object* v_initHeartbeats_572_; lean_object* v_maxHeartbeats_573_; lean_object* v_quotContext_574_; lean_object* v_currMacroScope_575_; lean_object* v_cancelTk_x3f_576_; lean_object* v_inheritedTraceOptions_577_; lean_object* v_currRecDepth_578_; lean_object* v_ref_579_; uint8_t v_suppressElabErrors_580_; uint8_t v_isRecordingDeps_581_; lean_object* v___y_582_; lean_object* v___x_599_; uint8_t v___y_601_; lean_object* v_env_623_; uint8_t v___x_624_; uint16_t v___x_625_; uint16_t v___x_626_; uint16_t v___x_627_; uint8_t v___x_628_; 
v___x_486_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_487_ = 0;
v___x_488_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(v_options_474_, v___x_486_, v___x_487_);
v___x_566_ = l_Lean_OptionFlags_ofOptions(v___x_488_);
v___x_599_ = lean_st_ref_get(v___y_462_);
v_env_623_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_599_);
v___x_624_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_623_);
lean_dec_ref(v_env_623_);
v___x_625_ = 512;
v___x_626_ = lean_uint16_land(v___x_566_, v___x_625_);
v___x_627_ = 0;
v___x_628_ = lean_uint16_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
if (v___x_624_ == 0)
{
v___y_601_ = v___x_456_;
goto v___jp_600_;
}
else
{
v_fileName_568_ = v_fileName_472_;
v_fileMap_569_ = v_fileMap_473_;
v_currNamespace_570_ = v_currNamespace_475_;
v_openDecls_571_ = v_openDecls_476_;
v_initHeartbeats_572_ = v_initHeartbeats_477_;
v_maxHeartbeats_573_ = v_maxHeartbeats_478_;
v_quotContext_574_ = v_quotContext_479_;
v_currMacroScope_575_ = v_currMacroScope_480_;
v_cancelTk_x3f_576_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_577_ = v_inheritedTraceOptions_482_;
v_currRecDepth_578_ = v_currRecDepth_465_;
v_ref_579_ = v_ref_466_;
v_suppressElabErrors_580_ = v_suppressElabErrors_467_;
v_isRecordingDeps_581_ = v_isRecordingDeps_468_;
v___y_582_ = v___y_462_;
goto v___jp_567_;
}
}
else
{
if (v___x_624_ == 0)
{
v_fileName_568_ = v_fileName_472_;
v_fileMap_569_ = v_fileMap_473_;
v_currNamespace_570_ = v_currNamespace_475_;
v_openDecls_571_ = v_openDecls_476_;
v_initHeartbeats_572_ = v_initHeartbeats_477_;
v_maxHeartbeats_573_ = v_maxHeartbeats_478_;
v_quotContext_574_ = v_quotContext_479_;
v_currMacroScope_575_ = v_currMacroScope_480_;
v_cancelTk_x3f_576_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_577_ = v_inheritedTraceOptions_482_;
v_currRecDepth_578_ = v_currRecDepth_465_;
v_ref_579_ = v_ref_466_;
v_suppressElabErrors_580_ = v_suppressElabErrors_467_;
v_isRecordingDeps_581_ = v_isRecordingDeps_468_;
v___y_582_ = v___y_462_;
goto v___jp_567_;
}
else
{
v___y_601_ = v___x_487_;
goto v___jp_600_;
}
}
v___jp_489_:
{
lean_object* v___x_496_; double v___x_497_; double v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_496_ = lean_io_get_num_heartbeats();
v___x_497_ = lean_float_of_nat(v___y_493_);
v___x_498_ = lean_float_of_nat(v___x_496_);
v___x_499_ = lean_box_float(v___x_497_);
v___x_500_ = lean_box_float(v___x_498_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_495_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_455_, v___x_456_, v___x_457_, v___x_488_, v___y_492_, v___y_491_, v___f_458_, v___x_502_, v___y_490_, v___y_494_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v___x_488_);
return v___x_503_;
}
v___jp_504_:
{
lean_object* v___x_511_; double v___x_512_; double v___x_513_; double v___x_514_; double v___x_515_; double v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_511_ = lean_io_mono_nanos_now();
v___x_512_ = lean_float_of_nat(v___y_508_);
v___x_513_ = lean_float_once(&l_Lean_Compiler_compile___lam__1___closed__0, &l_Lean_Compiler_compile___lam__1___closed__0_once, _init_l_Lean_Compiler_compile___lam__1___closed__0);
v___x_514_ = lean_float_div(v___x_512_, v___x_513_);
v___x_515_ = lean_float_of_nat(v___x_511_);
v___x_516_ = lean_float_div(v___x_515_, v___x_513_);
v___x_517_ = lean_box_float(v___x_514_);
v___x_518_ = lean_box_float(v___x_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_510_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_455_, v___x_456_, v___x_457_, v___x_488_, v___y_507_, v___y_506_, v___f_458_, v___x_520_, v___y_505_, v___y_509_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v___x_488_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__3___redArg(v___y_525_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = l_Lean_trace_profiler_useHeartbeats;
v___x_529_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(v___x_488_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_io_mono_nanos_now();
v___x_531_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___y_523_, v___y_525_);
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
v___y_505_ = v___y_523_;
v___y_506_ = v_a_527_;
v___y_507_ = v___y_524_;
v___y_508_ = v___x_530_;
v___y_509_ = v___y_525_;
v_a_510_ = v___x_537_;
goto v___jp_504_;
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
v___y_505_ = v___y_523_;
v___y_506_ = v_a_527_;
v___y_507_ = v___y_524_;
v___y_508_ = v___x_530_;
v___y_509_ = v___y_525_;
v_a_510_ = v___x_545_;
goto v___jp_504_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_io_get_num_heartbeats();
v___x_549_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___y_523_, v___y_525_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 1);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v___y_490_ = v___y_523_;
v___y_491_ = v_a_527_;
v___y_492_ = v___y_524_;
v___y_493_ = v___x_548_;
v___y_494_ = v___y_525_;
v_a_495_ = v___x_555_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_a_558_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_549_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_549_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v___y_490_ = v___y_523_;
v___y_491_ = v_a_527_;
v___y_492_ = v___y_524_;
v___y_493_ = v___x_548_;
v___y_494_ = v___y_525_;
v_a_495_ = v___x_563_;
goto v___jp_489_;
}
}
}
}
}
v___jp_567_:
{
uint8_t v_hasTrace_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_hasTrace_583_ = lean_ctor_get_uint8(v___x_488_, sizeof(void*)*1);
v___x_584_ = l_Lean_maxRecDepth;
v___x_585_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v___x_488_, v___x_584_);
lean_inc_ref(v_inheritedTraceOptions_577_);
lean_inc_ref(v___x_488_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 11, v_inheritedTraceOptions_577_);
lean_ctor_set(v___x_484_, 10, v_cancelTk_x3f_576_);
lean_ctor_set(v___x_484_, 9, v_currMacroScope_575_);
lean_ctor_set(v___x_484_, 8, v_quotContext_574_);
lean_ctor_set(v___x_484_, 7, v_maxHeartbeats_573_);
lean_ctor_set(v___x_484_, 6, v_initHeartbeats_572_);
lean_ctor_set(v___x_484_, 5, v_openDecls_571_);
lean_ctor_set(v___x_484_, 4, v_currNamespace_570_);
lean_ctor_set(v___x_484_, 3, v___x_585_);
lean_ctor_set(v___x_484_, 2, v___x_488_);
lean_ctor_set(v___x_484_, 1, v_fileMap_569_);
lean_ctor_set(v___x_484_, 0, v_fileName_568_);
v___x_587_ = v___x_484_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_fileName_568_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_fileMap_569_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_currNamespace_570_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_openDecls_571_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_initHeartbeats_572_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_maxHeartbeats_573_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_quotContext_574_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_currMacroScope_575_);
lean_ctor_set(v_reuseFailAlloc_598_, 10, v_cancelTk_x3f_576_);
lean_ctor_set(v_reuseFailAlloc_598_, 11, v_inheritedTraceOptions_577_);
v___x_587_ = v_reuseFailAlloc_598_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 2, v_ref_579_);
lean_ctor_set(v___x_470_, 1, v_currRecDepth_578_);
lean_ctor_set(v___x_470_, 0, v___x_587_);
v___x_589_ = v___x_470_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_currRecDepth_578_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_ref_579_);
v___x_589_ = v_reuseFailAlloc_597_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_ctor_set_uint16(v___x_589_, sizeof(void*)*3, v___x_566_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*3 + 2, v_suppressElabErrors_580_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*3 + 3, v_isRecordingDeps_581_);
if (v_hasTrace_583_ == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v_inheritedTraceOptions_577_);
lean_dec_ref(v___x_488_);
lean_dec_ref(v___f_458_);
lean_dec_ref(v___x_457_);
lean_dec(v___x_455_);
v___x_590_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___x_589_, v___y_582_);
lean_dec_ref(v___x_589_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1));
lean_inc(v___x_455_);
v___x_592_ = l_Lean_Name_append(v___x_591_, v___x_455_);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_577_, v___x_488_, v___x_592_);
lean_dec(v___x_592_);
lean_dec_ref(v_inheritedTraceOptions_577_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_trace_profiler;
v___x_595_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__4(v___x_488_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v___x_488_);
lean_dec_ref(v___f_458_);
lean_dec_ref(v___x_457_);
lean_dec(v___x_455_);
v___x_596_ = l_Lean_Compiler_LCNF_main(v_declNames_459_, v___x_460_, v___x_589_, v___y_582_);
lean_dec_ref(v___x_589_);
return v___x_596_;
}
else
{
v___y_523_ = v___x_589_;
v___y_524_ = v___x_593_;
v___y_525_ = v___y_582_;
goto v___jp_522_;
}
}
else
{
v___y_523_ = v___x_589_;
v___y_524_ = v___x_593_;
v___y_525_ = v___y_582_;
goto v___jp_522_;
}
}
}
}
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v_env_603_; lean_object* v_nextMacroScope_604_; lean_object* v_ngen_605_; lean_object* v_auxDeclNGen_606_; lean_object* v_traceState_607_; lean_object* v_recordedDeps_608_; lean_object* v_messages_609_; lean_object* v_infoState_610_; lean_object* v_snapshotTasks_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
v___x_602_ = lean_st_ref_take(v___y_462_);
v_env_603_ = lean_ctor_get(v___x_602_, 0);
v_nextMacroScope_604_ = lean_ctor_get(v___x_602_, 1);
v_ngen_605_ = lean_ctor_get(v___x_602_, 2);
v_auxDeclNGen_606_ = lean_ctor_get(v___x_602_, 3);
v_traceState_607_ = lean_ctor_get(v___x_602_, 4);
v_recordedDeps_608_ = lean_ctor_get(v___x_602_, 6);
v_messages_609_ = lean_ctor_get(v___x_602_, 7);
v_infoState_610_ = lean_ctor_get(v___x_602_, 8);
v_snapshotTasks_611_ = lean_ctor_get(v___x_602_, 9);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_602_, 5);
lean_dec(v_unused_622_);
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snapshotTasks_611_);
lean_inc(v_infoState_610_);
lean_inc(v_messages_609_);
lean_inc(v_recordedDeps_608_);
lean_inc(v_traceState_607_);
lean_inc(v_auxDeclNGen_606_);
lean_inc(v_ngen_605_);
lean_inc(v_nextMacroScope_604_);
lean_inc(v_env_603_);
lean_dec(v___x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_615_ = l_Lean_Kernel_enableDiag(v_env_603_, v___y_601_);
v___x_616_ = lean_obj_once(&l_Lean_Compiler_compile___lam__1___closed__2, &l_Lean_Compiler_compile___lam__1___closed__2_once, _init_l_Lean_Compiler_compile___lam__1___closed__2);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 5, v___x_616_);
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_nextMacroScope_604_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_ngen_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_auxDeclNGen_606_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_traceState_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_recordedDeps_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_messages_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_infoState_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 9, v_snapshotTasks_611_);
v___x_618_ = v_reuseFailAlloc_620_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = lean_st_ref_put(v___y_462_, v___x_618_);
v_fileName_568_ = v_fileName_472_;
v_fileMap_569_ = v_fileMap_473_;
v_currNamespace_570_ = v_currNamespace_475_;
v_openDecls_571_ = v_openDecls_476_;
v_initHeartbeats_572_ = v_initHeartbeats_477_;
v_maxHeartbeats_573_ = v_maxHeartbeats_478_;
v_quotContext_574_ = v_quotContext_479_;
v_currMacroScope_575_ = v_currMacroScope_480_;
v_cancelTk_x3f_576_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_577_ = v_inheritedTraceOptions_482_;
v_currRecDepth_578_ = v_currRecDepth_465_;
v_ref_579_ = v_ref_466_;
v_suppressElabErrors_580_ = v_suppressElabErrors_467_;
v_isRecordingDeps_581_ = v_isRecordingDeps_468_;
v___y_582_ = v___y_462_;
goto v___jp_567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1___boxed(lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___f_635_, lean_object* v_declNames_636_, lean_object* v___x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_7071__boxed_641_; lean_object* v_res_642_; 
v___x_7071__boxed_641_ = lean_unbox(v___x_633_);
v_res_642_ = l_Lean_Compiler_compile___lam__1(v___x_632_, v___x_7071__boxed_641_, v___x_634_, v___f_635_, v_declNames_636_, v___x_637_, v___y_638_, v___y_639_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___redArg(v_x_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_00_u03b1_674_, v_x_675_, v___y_676_, v___y_677_);
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

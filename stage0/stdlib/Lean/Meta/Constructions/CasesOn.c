// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOn
// Imports: public import Lean.AddDecl
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnImp___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_mkCasesOn___closed__0 = (const lean_object*)&l_Lean_mkCasesOn___closed__0_value;
static const lean_string_object l_Lean_mkCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCasesOn"};
static const lean_object* l_Lean_mkCasesOn___closed__1 = (const lean_object*)&l_Lean_mkCasesOn___closed__1_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkCasesOn___closed__2_value_aux_0),((lean_object*)&l_Lean_mkCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 62, 169, 32, 175, 179, 252, 201)}};
static const lean_object* l_Lean_mkCasesOn___closed__2 = (const lean_object*)&l_Lean_mkCasesOn___closed__2_value;
static const lean_string_object l_Lean_mkCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkCasesOn___closed__3 = (const lean_object*)&l_Lean_mkCasesOn___closed__3_value;
static lean_once_cell_t l_Lean_mkCasesOn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkCasesOn___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 138, 163, 69, 218, 172, 3, 193)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 93, 225, 44, 98, 194, 222, 198)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 210, 255, 39, 71, 150, 217, 233)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 108, 49, 213, 198, 16, 112, 74)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 136, 138, 61, 141, 154, 156, 94)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 243, 213, 167, 134, 227, 5, 96)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 216, 218, 215, 246, 206, 35, 172)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 250, 31, 145, 63, 77, 70, 221)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 98, 44, 117, 252, 253, 129, 45)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(989523109) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(33, 63, 231, 116, 95, 206, 102, 190)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 168, 149, 82, 136, 252, 169, 218)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 82, 99, 185, 147, 204, 210, 220)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(191, 22, 202, 159, 104, 165, 236, 145)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnImp___boxed(lean_object* v_env_3_, lean_object* v_declName_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_mk_cases_on(v_env_3_, v_declName_4_);
lean_dec(v_declName_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(lean_object* v_cls_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_options_12_; uint8_t v_hasTrace_13_; 
v_options_12_ = lean_ctor_get(v___y_10_, 2);
v_hasTrace_13_ = lean_ctor_get_uint8(v_options_12_, sizeof(void*)*1);
if (v_hasTrace_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_cls_9_);
v___x_14_ = lean_box(v_hasTrace_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v_inheritedTraceOptions_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_inheritedTraceOptions_16_ = lean_ctor_get(v___y_10_, 13);
v___x_17_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___closed__1));
v___x_18_ = l_Lean_Name_append(v___x_17_, v_cls_9_);
v___x_19_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_16_, v_options_12_, v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object* v_cls_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(v_cls_22_, v___y_23_);
lean_dec_ref(v___y_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2(lean_object* v_cls_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(v_cls_26_, v___y_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___boxed(lean_object* v_cls_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2(v_cls_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(32u);
v___x_41_ = lean_mk_empty_array_with_capacity(v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_43_ = ((size_t)5ULL);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_unsigned_to_nat(32u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
v___x_47_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__0);
v___x_48_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_44_);
lean_ctor_set(v___x_48_, 3, v___x_44_);
lean_ctor_set_usize(v___x_48_, 4, v___x_43_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; lean_object* v_traceState_52_; lean_object* v_traces_53_; lean_object* v___x_54_; lean_object* v_traceState_55_; lean_object* v_env_56_; lean_object* v_nextMacroScope_57_; lean_object* v_ngen_58_; lean_object* v_auxDeclNGen_59_; lean_object* v_cache_60_; lean_object* v_messages_61_; lean_object* v_infoState_62_; lean_object* v_snapshotTasks_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_82_; 
v___x_51_ = lean_st_ref_get(v___y_49_);
v_traceState_52_ = lean_ctor_get(v___x_51_, 4);
lean_inc_ref(v_traceState_52_);
lean_dec(v___x_51_);
v_traces_53_ = lean_ctor_get(v_traceState_52_, 0);
lean_inc_ref(v_traces_53_);
lean_dec_ref(v_traceState_52_);
v___x_54_ = lean_st_ref_take(v___y_49_);
v_traceState_55_ = lean_ctor_get(v___x_54_, 4);
v_env_56_ = lean_ctor_get(v___x_54_, 0);
v_nextMacroScope_57_ = lean_ctor_get(v___x_54_, 1);
v_ngen_58_ = lean_ctor_get(v___x_54_, 2);
v_auxDeclNGen_59_ = lean_ctor_get(v___x_54_, 3);
v_cache_60_ = lean_ctor_get(v___x_54_, 5);
v_messages_61_ = lean_ctor_get(v___x_54_, 6);
v_infoState_62_ = lean_ctor_get(v___x_54_, 7);
v_snapshotTasks_63_ = lean_ctor_get(v___x_54_, 8);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_82_ == 0)
{
v___x_65_ = v___x_54_;
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snapshotTasks_63_);
lean_inc(v_infoState_62_);
lean_inc(v_messages_61_);
lean_inc(v_cache_60_);
lean_inc(v_traceState_55_);
lean_inc(v_auxDeclNGen_59_);
lean_inc(v_ngen_58_);
lean_inc(v_nextMacroScope_57_);
lean_inc(v_env_56_);
lean_dec(v___x_54_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint64_t v_tid_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_80_; 
v_tid_67_ = lean_ctor_get_uint64(v_traceState_55_, sizeof(void*)*1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_traceState_55_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_traceState_55_, 0);
lean_dec(v_unused_81_);
v___x_69_ = v_traceState_55_;
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_traceState_55_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___closed__1);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_71_);
lean_ctor_set_uint64(v_reuseFailAlloc_79_, sizeof(void*)*1, v_tid_67_);
v___x_73_ = v_reuseFailAlloc_79_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_75_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 4, v___x_73_);
v___x_75_ = v___x_65_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_env_56_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_nextMacroScope_57_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v_ngen_58_);
lean_ctor_set(v_reuseFailAlloc_78_, 3, v_auxDeclNGen_59_);
lean_ctor_set(v_reuseFailAlloc_78_, 4, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_78_, 5, v_cache_60_);
lean_ctor_set(v_reuseFailAlloc_78_, 6, v_messages_61_);
lean_ctor_set(v_reuseFailAlloc_78_, 7, v_infoState_62_);
lean_ctor_set(v_reuseFailAlloc_78_, 8, v_snapshotTasks_63_);
v___x_75_ = v_reuseFailAlloc_78_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_st_ref_set(v___y_49_, v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_traces_53_);
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg___boxed(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(v___y_83_);
lean_dec(v___y_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3(lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___boxed(lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3(v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(lean_object* v_opts_98_, lean_object* v_opt_99_){
_start:
{
lean_object* v_name_100_; lean_object* v_defValue_101_; lean_object* v_map_102_; lean_object* v___x_103_; 
v_name_100_ = lean_ctor_get(v_opt_99_, 0);
v_defValue_101_ = lean_ctor_get(v_opt_99_, 1);
v_map_102_ = lean_ctor_get(v_opts_98_, 0);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_102_, v_name_100_);
if (lean_obj_tag(v___x_103_) == 0)
{
uint8_t v___x_104_; 
v___x_104_ = lean_unbox(v_defValue_101_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v___x_103_);
if (lean_obj_tag(v_val_105_) == 1)
{
uint8_t v_v_106_; 
v_v_106_ = lean_ctor_get_uint8(v_val_105_, 0);
lean_dec_ref(v_val_105_);
return v_v_106_;
}
else
{
uint8_t v___x_107_; 
lean_dec(v_val_105_);
v___x_107_ = lean_unbox(v_defValue_101_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_opts_108_, lean_object* v_opt_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_opts_108_, v_opt_109_);
lean_dec_ref(v_opt_109_);
lean_dec_ref(v_opts_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object* v_declName_112_, lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = l_Lean_MessageData_ofName(v_declName_112_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object* v_declName_121_, lean_object* v_x_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_mkCasesOn___lam__0(v_declName_121_, v_x_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec_ref(v_x_122_);
return v_res_128_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_box(0);
v___x_130_ = l_Lean_interruptExceptionId;
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg(){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___closed__0);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg();
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(lean_object* v_msgData_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_env_144_; lean_object* v___x_145_; lean_object* v_mctx_146_; lean_object* v_lctx_147_; lean_object* v_options_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_143_ = lean_st_ref_get(v___y_141_);
v_env_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_ref(v_env_144_);
lean_dec(v___x_143_);
v___x_145_ = lean_st_ref_get(v___y_139_);
v_mctx_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_mctx_146_);
lean_dec(v___x_145_);
v_lctx_147_ = lean_ctor_get(v___y_138_, 2);
v_options_148_ = lean_ctor_get(v___y_140_, 2);
lean_inc_ref(v_options_148_);
lean_inc_ref(v_lctx_147_);
v___x_149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_149_, 0, v_env_144_);
lean_ctor_set(v___x_149_, 1, v_mctx_146_);
lean_ctor_set(v___x_149_, 2, v_lctx_147_);
lean_ctor_set(v___x_149_, 3, v_options_148_);
v___x_150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_msgData_137_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12___boxed(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(v_msgData_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_ref_165_; lean_object* v___x_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_ref_165_ = lean_ctor_get(v___y_162_, 5);
v___x_166_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_inc(v_ref_165_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_165_);
lean_ctor_set(v___x_171_, 1, v_a_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object* v_ex_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; 
if (lean_obj_tag(v_ex_183_) == 16)
{
lean_object* v___x_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v___x_197_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg();
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_inc_ref(v___y_186_);
v___y_190_ = v___y_184_;
v___y_191_ = v___y_185_;
v___y_192_ = v___y_186_;
v___y_193_ = v___y_187_;
goto v___jp_189_;
}
v___jp_189_:
{
lean_object* v_options_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_options_194_ = lean_ctor_get(v___y_192_, 2);
lean_inc_ref(v_options_194_);
v___x_195_ = l_Lean_Kernel_Exception_toMessageData(v_ex_183_, v_options_194_);
v___x_196_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(v___x_195_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_ex_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_a_219_);
lean_dec_ref(v_x_213_);
v___x_220_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_a_219_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
return v___x_220_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v_x_213_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v_x_213_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v_x_213_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 0);
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_236_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
lean_ctor_set(v___x_242_, 3, v___x_241_);
lean_ctor_set(v___x_242_, 4, v___x_241_);
lean_ctor_set(v___x_242_, 5, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object* v_declName_243_, uint8_t v_s_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_env_249_; lean_object* v_nextMacroScope_250_; lean_object* v_ngen_251_; lean_object* v_auxDeclNGen_252_; lean_object* v_traceState_253_; lean_object* v_messages_254_; lean_object* v_infoState_255_; lean_object* v_snapshotTasks_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_285_; 
v___x_248_ = lean_st_ref_take(v___y_246_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
v_nextMacroScope_250_ = lean_ctor_get(v___x_248_, 1);
v_ngen_251_ = lean_ctor_get(v___x_248_, 2);
v_auxDeclNGen_252_ = lean_ctor_get(v___x_248_, 3);
v_traceState_253_ = lean_ctor_get(v___x_248_, 4);
v_messages_254_ = lean_ctor_get(v___x_248_, 6);
v_infoState_255_ = lean_ctor_get(v___x_248_, 7);
v_snapshotTasks_256_ = lean_ctor_get(v___x_248_, 8);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_248_, 5);
lean_dec(v_unused_286_);
v___x_258_ = v___x_248_;
v_isShared_259_ = v_isSharedCheck_285_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snapshotTasks_256_);
lean_inc(v_infoState_255_);
lean_inc(v_messages_254_);
lean_inc(v_traceState_253_);
lean_inc(v_auxDeclNGen_252_);
lean_inc(v_ngen_251_);
lean_inc(v_nextMacroScope_250_);
lean_inc(v_env_249_);
lean_dec(v___x_248_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_285_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_260_ = 0;
v___x_261_ = lean_box(0);
v___x_262_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_249_, v_declName_243_, v_s_244_, v___x_260_, v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 5, v___x_263_);
lean_ctor_set(v___x_258_, 0, v___x_262_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_nextMacroScope_250_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_ngen_251_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_auxDeclNGen_252_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_traceState_253_);
lean_ctor_set(v_reuseFailAlloc_284_, 5, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_284_, 6, v_messages_254_);
lean_ctor_set(v_reuseFailAlloc_284_, 7, v_infoState_255_);
lean_ctor_set(v_reuseFailAlloc_284_, 8, v_snapshotTasks_256_);
v___x_265_ = v_reuseFailAlloc_284_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_mctx_268_; lean_object* v_zetaDeltaFVarIds_269_; lean_object* v_postponed_270_; lean_object* v_diag_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
v___x_266_ = lean_st_ref_set(v___y_246_, v___x_265_);
v___x_267_ = lean_st_ref_take(v___y_245_);
v_mctx_268_ = lean_ctor_get(v___x_267_, 0);
v_zetaDeltaFVarIds_269_ = lean_ctor_get(v___x_267_, 2);
v_postponed_270_ = lean_ctor_get(v___x_267_, 3);
v_diag_271_ = lean_ctor_get(v___x_267_, 4);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_267_, 1);
lean_dec(v_unused_283_);
v___x_273_ = v___x_267_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_diag_271_);
lean_inc(v_postponed_270_);
lean_inc(v_zetaDeltaFVarIds_269_);
lean_inc(v_mctx_268_);
lean_dec(v___x_267_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_mctx_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_zetaDeltaFVarIds_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_postponed_270_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_diag_271_);
v___x_277_ = v_reuseFailAlloc_281_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_st_ref_set(v___y_245_, v___x_277_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_declName_287_, lean_object* v_s_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_s_boxed_292_; lean_object* v_res_293_; 
v_s_boxed_292_ = lean_unbox(v_s_288_);
v_res_293_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_287_, v_s_boxed_292_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v___y_289_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(lean_object* v_declName_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v___x_300_; lean_object* v___x_301_; 
v___x_300_ = 0;
v___x_301_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_294_, v___x_300_, v___y_296_, v___y_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_declName_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_declName_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11(size_t v_sz_309_, size_t v_i_310_, lean_object* v_bs_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_lt(v_i_310_, v_sz_309_);
if (v___x_312_ == 0)
{
return v_bs_311_;
}
else
{
lean_object* v_v_313_; lean_object* v_msg_314_; lean_object* v___x_315_; lean_object* v_bs_x27_316_; size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v_v_313_ = lean_array_uget_borrowed(v_bs_311_, v_i_310_);
v_msg_314_ = lean_ctor_get(v_v_313_, 1);
lean_inc_ref(v_msg_314_);
v___x_315_ = lean_unsigned_to_nat(0u);
v_bs_x27_316_ = lean_array_uset(v_bs_311_, v_i_310_, v___x_315_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_i_310_, v___x_317_);
v___x_319_ = lean_array_uset(v_bs_x27_316_, v_i_310_, v_msg_314_);
v_i_310_ = v___x_318_;
v_bs_311_ = v___x_319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11___boxed(lean_object* v_sz_321_, lean_object* v_i_322_, lean_object* v_bs_323_){
_start:
{
size_t v_sz_boxed_324_; size_t v_i_boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_324_ = lean_unbox_usize(v_sz_321_);
lean_dec(v_sz_321_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11(v_sz_boxed_324_, v_i_boxed_325_, v_bs_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(lean_object* v_oldTraces_327_, lean_object* v_data_328_, lean_object* v_ref_329_, lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_currRecDepth_339_; lean_object* v_maxRecDepth_340_; lean_object* v_ref_341_; lean_object* v_currNamespace_342_; lean_object* v_openDecls_343_; lean_object* v_initHeartbeats_344_; lean_object* v_maxHeartbeats_345_; lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; uint8_t v_diag_348_; lean_object* v_cancelTk_x3f_349_; uint8_t v_suppressElabErrors_350_; lean_object* v_inheritedTraceOptions_351_; lean_object* v___x_352_; lean_object* v_traceState_353_; lean_object* v_traces_354_; lean_object* v_ref_355_; lean_object* v___x_356_; lean_object* v___x_357_; size_t v_sz_358_; size_t v___x_359_; lean_object* v___x_360_; lean_object* v_msg_361_; lean_object* v___x_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_400_; 
v_fileName_336_ = lean_ctor_get(v___y_333_, 0);
v_fileMap_337_ = lean_ctor_get(v___y_333_, 1);
v_options_338_ = lean_ctor_get(v___y_333_, 2);
v_currRecDepth_339_ = lean_ctor_get(v___y_333_, 3);
v_maxRecDepth_340_ = lean_ctor_get(v___y_333_, 4);
v_ref_341_ = lean_ctor_get(v___y_333_, 5);
v_currNamespace_342_ = lean_ctor_get(v___y_333_, 6);
v_openDecls_343_ = lean_ctor_get(v___y_333_, 7);
v_initHeartbeats_344_ = lean_ctor_get(v___y_333_, 8);
v_maxHeartbeats_345_ = lean_ctor_get(v___y_333_, 9);
v_quotContext_346_ = lean_ctor_get(v___y_333_, 10);
v_currMacroScope_347_ = lean_ctor_get(v___y_333_, 11);
v_diag_348_ = lean_ctor_get_uint8(v___y_333_, sizeof(void*)*14);
v_cancelTk_x3f_349_ = lean_ctor_get(v___y_333_, 12);
v_suppressElabErrors_350_ = lean_ctor_get_uint8(v___y_333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_351_ = lean_ctor_get(v___y_333_, 13);
v___x_352_ = lean_st_ref_get(v___y_334_);
v_traceState_353_ = lean_ctor_get(v___x_352_, 4);
lean_inc_ref(v_traceState_353_);
lean_dec(v___x_352_);
v_traces_354_ = lean_ctor_get(v_traceState_353_, 0);
lean_inc_ref(v_traces_354_);
lean_dec_ref(v_traceState_353_);
v_ref_355_ = l_Lean_replaceRef(v_ref_329_, v_ref_341_);
lean_inc_ref(v_inheritedTraceOptions_351_);
lean_inc(v_cancelTk_x3f_349_);
lean_inc(v_currMacroScope_347_);
lean_inc(v_quotContext_346_);
lean_inc(v_maxHeartbeats_345_);
lean_inc(v_initHeartbeats_344_);
lean_inc(v_openDecls_343_);
lean_inc(v_currNamespace_342_);
lean_inc(v_maxRecDepth_340_);
lean_inc(v_currRecDepth_339_);
lean_inc_ref(v_options_338_);
lean_inc_ref(v_fileMap_337_);
lean_inc_ref(v_fileName_336_);
v___x_356_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_356_, 0, v_fileName_336_);
lean_ctor_set(v___x_356_, 1, v_fileMap_337_);
lean_ctor_set(v___x_356_, 2, v_options_338_);
lean_ctor_set(v___x_356_, 3, v_currRecDepth_339_);
lean_ctor_set(v___x_356_, 4, v_maxRecDepth_340_);
lean_ctor_set(v___x_356_, 5, v_ref_355_);
lean_ctor_set(v___x_356_, 6, v_currNamespace_342_);
lean_ctor_set(v___x_356_, 7, v_openDecls_343_);
lean_ctor_set(v___x_356_, 8, v_initHeartbeats_344_);
lean_ctor_set(v___x_356_, 9, v_maxHeartbeats_345_);
lean_ctor_set(v___x_356_, 10, v_quotContext_346_);
lean_ctor_set(v___x_356_, 11, v_currMacroScope_347_);
lean_ctor_set(v___x_356_, 12, v_cancelTk_x3f_349_);
lean_ctor_set(v___x_356_, 13, v_inheritedTraceOptions_351_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14, v_diag_348_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14 + 1, v_suppressElabErrors_350_);
v___x_357_ = l_Lean_PersistentArray_toArray___redArg(v_traces_354_);
lean_dec_ref(v_traces_354_);
v_sz_358_ = lean_array_size(v___x_357_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11(v_sz_358_, v___x_359_, v___x_357_);
v_msg_361_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_361_, 0, v_data_328_);
lean_ctor_set(v_msg_361_, 1, v_msg_330_);
lean_ctor_set(v_msg_361_, 2, v___x_360_);
v___x_362_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(v_msg_361_, v___y_331_, v___y_332_, v___x_356_, v___y_334_);
lean_dec_ref(v___x_356_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_400_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_400_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_400_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v_traceState_368_; lean_object* v_env_369_; lean_object* v_nextMacroScope_370_; lean_object* v_ngen_371_; lean_object* v_auxDeclNGen_372_; lean_object* v_cache_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_399_; 
v___x_367_ = lean_st_ref_take(v___y_334_);
v_traceState_368_ = lean_ctor_get(v___x_367_, 4);
v_env_369_ = lean_ctor_get(v___x_367_, 0);
v_nextMacroScope_370_ = lean_ctor_get(v___x_367_, 1);
v_ngen_371_ = lean_ctor_get(v___x_367_, 2);
v_auxDeclNGen_372_ = lean_ctor_get(v___x_367_, 3);
v_cache_373_ = lean_ctor_get(v___x_367_, 5);
v_messages_374_ = lean_ctor_get(v___x_367_, 6);
v_infoState_375_ = lean_ctor_get(v___x_367_, 7);
v_snapshotTasks_376_ = lean_ctor_get(v___x_367_, 8);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_399_ == 0)
{
v___x_378_ = v___x_367_;
v_isShared_379_ = v_isSharedCheck_399_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_cache_373_);
lean_inc(v_traceState_368_);
lean_inc(v_auxDeclNGen_372_);
lean_inc(v_ngen_371_);
lean_inc(v_nextMacroScope_370_);
lean_inc(v_env_369_);
lean_dec(v___x_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_399_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint64_t v_tid_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_397_; 
v_tid_380_ = lean_ctor_get_uint64(v_traceState_368_, sizeof(void*)*1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_traceState_368_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_traceState_368_, 0);
lean_dec(v_unused_398_);
v___x_382_ = v_traceState_368_;
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
else
{
lean_dec(v_traceState_368_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_ref_329_);
lean_ctor_set(v___x_384_, 1, v_a_363_);
v___x_385_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_327_, v___x_384_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_385_);
lean_ctor_set_uint64(v_reuseFailAlloc_396_, sizeof(void*)*1, v_tid_380_);
v___x_387_ = v_reuseFailAlloc_396_;
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
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_env_369_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_nextMacroScope_370_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_ngen_371_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_auxDeclNGen_372_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_cache_373_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_snapshotTasks_376_);
v___x_389_ = v_reuseFailAlloc_395_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_st_ref_set(v___y_334_, v___x_389_);
v___x_391_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_391_);
v___x_393_ = v___x_365_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8___boxed(lean_object* v_oldTraces_401_, lean_object* v_data_402_, lean_object* v_ref_403_, lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(v_oldTraces_401_, v_data_402_, v_ref_403_, v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(lean_object* v_opts_411_, lean_object* v_opt_412_){
_start:
{
lean_object* v_name_413_; lean_object* v_defValue_414_; lean_object* v_map_415_; lean_object* v___x_416_; 
v_name_413_ = lean_ctor_get(v_opt_412_, 0);
v_defValue_414_ = lean_ctor_get(v_opt_412_, 1);
v_map_415_ = lean_ctor_get(v_opts_411_, 0);
v___x_416_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_415_, v_name_413_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_inc(v_defValue_414_);
return v_defValue_414_;
}
else
{
lean_object* v_val_417_; 
v_val_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_val_417_);
lean_dec_ref(v___x_416_);
if (lean_obj_tag(v_val_417_) == 3)
{
lean_object* v_v_418_; 
v_v_418_ = lean_ctor_get(v_val_417_, 0);
lean_inc(v_v_418_);
lean_dec_ref(v_val_417_);
return v_v_418_;
}
else
{
lean_dec(v_val_417_);
lean_inc(v_defValue_414_);
return v_defValue_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10___boxed(lean_object* v_opts_419_, lean_object* v_opt_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_419_, v_opt_420_);
lean_dec_ref(v_opt_420_);
lean_dec_ref(v_opts_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v_x_422_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v_x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_x_422_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v_x_422_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg___boxed(lean_object* v_x_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_x_440_);
return v_res_442_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(lean_object* v_e_443_){
_start:
{
if (lean_obj_tag(v_e_443_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = 2;
return v___x_444_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7___boxed(lean_object* v_e_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(v_e_446_);
lean_dec_ref(v_e_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__0));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2(void){
_start:
{
lean_object* v___x_452_; double v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_float_of_nat(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__3));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5(void){
_start:
{
lean_object* v___x_457_; double v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(1000u);
v___x_458_ = lean_float_of_nat(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(lean_object* v_cls_459_, uint8_t v_collapsed_460_, lean_object* v_tag_461_, lean_object* v_opts_462_, uint8_t v_clsEnabled_463_, lean_object* v_oldTraces_464_, lean_object* v_msg_465_, lean_object* v_resStartStop_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_563_; 
v_fst_472_ = lean_ctor_get(v_resStartStop_466_, 0);
v_snd_473_ = lean_ctor_get(v_resStartStop_466_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_resStartStop_466_);
if (v_isSharedCheck_563_ == 0)
{
v___x_475_ = v_resStartStop_466_;
v_isShared_476_ = v_isSharedCheck_563_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
lean_dec(v_resStartStop_466_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_563_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v_data_480_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_562_; 
v_fst_483_ = lean_ctor_get(v_snd_473_, 0);
v_snd_484_ = lean_ctor_get(v_snd_473_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_snd_473_);
if (v_isSharedCheck_562_ == 0)
{
v___x_486_ = v_snd_473_;
v_isShared_487_ = v_isSharedCheck_562_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_snd_473_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_562_;
goto v_resetjp_485_;
}
v___jp_477_:
{
lean_object* v___x_481_; 
lean_inc(v___y_479_);
v___x_481_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(v_oldTraces_464_, v_data_480_, v___y_479_, v___y_478_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v___x_481_);
v___x_482_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_fst_472_);
return v___x_482_;
}
else
{
lean_dec(v_fst_472_);
return v___x_481_;
}
}
v_resetjp_485_:
{
lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___y_491_; lean_object* v_a_492_; uint8_t v___y_516_; double v___y_547_; 
v___x_488_ = l_Lean_trace_profiler;
v___x_489_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_opts_462_, v___x_488_);
if (v___x_489_ == 0)
{
v___y_516_ = v___x_489_;
goto v___jp_515_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = l_Lean_trace_profiler_useHeartbeats;
v___x_553_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_opts_462_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; double v___x_556_; double v___x_557_; double v___x_558_; 
v___x_554_ = l_Lean_trace_profiler_threshold;
v___x_555_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_462_, v___x_554_);
v___x_556_ = lean_float_of_nat(v___x_555_);
v___x_557_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5);
v___x_558_ = lean_float_div(v___x_556_, v___x_557_);
v___y_547_ = v___x_558_;
goto v___jp_546_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; double v___x_561_; 
v___x_559_ = l_Lean_trace_profiler_threshold;
v___x_560_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_462_, v___x_559_);
v___x_561_ = lean_float_of_nat(v___x_560_);
v___y_547_ = v___x_561_;
goto v___jp_546_;
}
}
v___jp_490_:
{
uint8_t v_result_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v_result_493_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(v_fst_472_);
v___x_494_ = l_Lean_TraceResult_toEmoji(v_result_493_);
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
v___x_496_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1);
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 7);
lean_ctor_set(v___x_486_, 1, v___x_496_);
lean_ctor_set(v___x_486_, 0, v___x_495_);
v___x_498_ = v___x_486_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_509_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v_m_500_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 7);
lean_ctor_set(v___x_475_, 1, v_a_492_);
lean_ctor_set(v___x_475_, 0, v___x_498_);
v_m_500_ = v___x_475_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_a_492_);
v_m_500_ = v_reuseFailAlloc_508_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; double v___x_503_; lean_object* v_data_504_; 
v___x_501_ = lean_box(v_result_493_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2);
lean_inc_ref(v_tag_461_);
lean_inc_ref(v___x_502_);
lean_inc(v_cls_459_);
v_data_504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_504_, 0, v_cls_459_);
lean_ctor_set(v_data_504_, 1, v___x_502_);
lean_ctor_set(v_data_504_, 2, v_tag_461_);
lean_ctor_set_float(v_data_504_, sizeof(void*)*3, v___x_503_);
lean_ctor_set_float(v_data_504_, sizeof(void*)*3 + 8, v___x_503_);
lean_ctor_set_uint8(v_data_504_, sizeof(void*)*3 + 16, v_collapsed_460_);
if (v___x_489_ == 0)
{
lean_dec_ref(v___x_502_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_dec_ref(v_tag_461_);
lean_dec(v_cls_459_);
v___y_478_ = v_m_500_;
v___y_479_ = v___y_491_;
v_data_480_ = v_data_504_;
goto v___jp_477_;
}
else
{
lean_object* v_data_505_; double v___x_506_; double v___x_507_; 
lean_dec_ref(v_data_504_);
v_data_505_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_505_, 0, v_cls_459_);
lean_ctor_set(v_data_505_, 1, v___x_502_);
lean_ctor_set(v_data_505_, 2, v_tag_461_);
v___x_506_ = lean_unbox_float(v_fst_483_);
lean_dec(v_fst_483_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3, v___x_506_);
v___x_507_ = lean_unbox_float(v_snd_484_);
lean_dec(v_snd_484_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3 + 8, v___x_507_);
lean_ctor_set_uint8(v_data_505_, sizeof(void*)*3 + 16, v_collapsed_460_);
v___y_478_ = v_m_500_;
v___y_479_ = v___y_491_;
v_data_480_ = v_data_505_;
goto v___jp_477_;
}
}
}
}
v___jp_510_:
{
lean_object* v_ref_511_; lean_object* v___x_512_; 
v_ref_511_ = lean_ctor_get(v___y_469_, 5);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v_fst_472_);
v___x_512_ = lean_apply_6(v_msg_465_, v_fst_472_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, lean_box(0));
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___y_491_ = v_ref_511_;
v_a_492_ = v_a_513_;
goto v___jp_490_;
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v___x_512_);
v___x_514_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4);
v___y_491_ = v_ref_511_;
v_a_492_ = v___x_514_;
goto v___jp_490_;
}
}
v___jp_515_:
{
if (v_clsEnabled_463_ == 0)
{
if (v___y_516_ == 0)
{
lean_object* v___x_517_; lean_object* v_traceState_518_; lean_object* v_env_519_; lean_object* v_nextMacroScope_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_cache_523_; lean_object* v_messages_524_; lean_object* v_infoState_525_; lean_object* v_snapshotTasks_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_545_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_475_);
lean_dec_ref(v_msg_465_);
lean_dec_ref(v_tag_461_);
lean_dec(v_cls_459_);
v___x_517_ = lean_st_ref_take(v___y_470_);
v_traceState_518_ = lean_ctor_get(v___x_517_, 4);
v_env_519_ = lean_ctor_get(v___x_517_, 0);
v_nextMacroScope_520_ = lean_ctor_get(v___x_517_, 1);
v_ngen_521_ = lean_ctor_get(v___x_517_, 2);
v_auxDeclNGen_522_ = lean_ctor_get(v___x_517_, 3);
v_cache_523_ = lean_ctor_get(v___x_517_, 5);
v_messages_524_ = lean_ctor_get(v___x_517_, 6);
v_infoState_525_ = lean_ctor_get(v___x_517_, 7);
v_snapshotTasks_526_ = lean_ctor_get(v___x_517_, 8);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_545_ == 0)
{
v___x_528_ = v___x_517_;
v_isShared_529_ = v_isSharedCheck_545_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snapshotTasks_526_);
lean_inc(v_infoState_525_);
lean_inc(v_messages_524_);
lean_inc(v_cache_523_);
lean_inc(v_traceState_518_);
lean_inc(v_auxDeclNGen_522_);
lean_inc(v_ngen_521_);
lean_inc(v_nextMacroScope_520_);
lean_inc(v_env_519_);
lean_dec(v___x_517_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_545_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint64_t v_tid_530_; lean_object* v_traces_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v_tid_530_ = lean_ctor_get_uint64(v_traceState_518_, sizeof(void*)*1);
v_traces_531_ = lean_ctor_get(v_traceState_518_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_traceState_518_);
if (v_isSharedCheck_544_ == 0)
{
v___x_533_ = v_traceState_518_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_traces_531_);
lean_dec(v_traceState_518_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_464_, v_traces_531_);
lean_dec_ref(v_traces_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_535_);
lean_ctor_set_uint64(v_reuseFailAlloc_543_, sizeof(void*)*1, v_tid_530_);
v___x_537_ = v_reuseFailAlloc_543_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v___x_537_);
v___x_539_ = v___x_528_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_env_519_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_nextMacroScope_520_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_cache_523_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_messages_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_infoState_525_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v_snapshotTasks_526_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_set(v___y_470_, v___x_539_);
v___x_541_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_fst_472_);
return v___x_541_;
}
}
}
}
}
else
{
goto v___jp_510_;
}
}
else
{
goto v___jp_510_;
}
}
v___jp_546_:
{
double v___x_548_; double v___x_549_; double v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unbox_float(v_snd_484_);
v___x_549_ = lean_unbox_float(v_fst_483_);
v___x_550_ = lean_float_sub(v___x_548_, v___x_549_);
v___x_551_ = lean_float_decLt(v___y_547_, v___x_550_);
v___y_516_ = v___x_551_;
goto v___jp_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___boxed(lean_object* v_cls_564_, lean_object* v_collapsed_565_, lean_object* v_tag_566_, lean_object* v_opts_567_, lean_object* v_clsEnabled_568_, lean_object* v_oldTraces_569_, lean_object* v_msg_570_, lean_object* v_resStartStop_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_collapsed_boxed_577_; uint8_t v_clsEnabled_boxed_578_; lean_object* v_res_579_; 
v_collapsed_boxed_577_ = lean_unbox(v_collapsed_565_);
v_clsEnabled_boxed_578_ = lean_unbox(v_clsEnabled_568_);
v_res_579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v_cls_564_, v_collapsed_boxed_577_, v_tag_566_, v_opts_567_, v_clsEnabled_boxed_578_, v_oldTraces_569_, v_msg_570_, v_resStartStop_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v_opts_567_);
return v_res_579_;
}
}
static double _init_l_Lean_mkCasesOn___closed__4(void){
_start:
{
lean_object* v___x_586_; double v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1000000000u);
v___x_587_ = lean_float_of_nat(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_options_594_; uint8_t v_hasTrace_595_; lean_object* v_name_596_; 
v_options_594_ = lean_ctor_get(v_a_591_, 2);
v_hasTrace_595_ = lean_ctor_get_uint8(v_options_594_, sizeof(void*)*1);
lean_inc(v_declName_588_);
v_name_596_ = l_Lean_mkCasesOnName(v_declName_588_);
if (v_hasTrace_595_ == 0)
{
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_597_ = lean_st_ref_get(v_a_592_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = lean_elab_environment_to_kernel_env(v_env_598_);
v___x_600_ = lean_mk_cases_on(v___x_599_, v_declName_588_);
lean_dec(v_declName_588_);
v___x_601_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_600_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___x_601_);
v___x_603_ = l_Lean_addDecl(v_a_602_, v_hasTrace_595_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_traceState_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v___x_603_);
lean_inc(v_name_596_);
v___x_604_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v___x_604_);
v___x_605_ = lean_st_ref_take(v_a_592_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_605_, 1);
v_ngen_608_ = lean_ctor_get(v___x_605_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_605_, 3);
v_traceState_610_ = lean_ctor_get(v___x_605_, 4);
v_messages_611_ = lean_ctor_get(v___x_605_, 6);
v_infoState_612_ = lean_ctor_get(v___x_605_, 7);
v_snapshotTasks_613_ = lean_ctor_get(v___x_605_, 8);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_605_, 5);
lean_dec(v_unused_640_);
v___x_615_ = v___x_605_;
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_traceState_610_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
lean_inc(v_name_596_);
v___x_617_ = l_Lean_markAuxRecursor(v_env_606_, v_name_596_);
v___x_618_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 5, v___x_618_);
lean_ctor_set(v___x_615_, 0, v___x_617_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_traceState_610_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v_snapshotTasks_613_);
v___x_620_ = v_reuseFailAlloc_638_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_mctx_623_; lean_object* v_zetaDeltaFVarIds_624_; lean_object* v_postponed_625_; lean_object* v_diag_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
v___x_621_ = lean_st_ref_set(v_a_592_, v___x_620_);
v___x_622_ = lean_st_ref_take(v_a_590_);
v_mctx_623_ = lean_ctor_get(v___x_622_, 0);
v_zetaDeltaFVarIds_624_ = lean_ctor_get(v___x_622_, 2);
v_postponed_625_ = lean_ctor_get(v___x_622_, 3);
v_diag_626_ = lean_ctor_get(v___x_622_, 4);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_622_, 1);
lean_dec(v_unused_637_);
v___x_628_ = v___x_622_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_diag_626_);
lean_inc(v_postponed_625_);
lean_inc(v_zetaDeltaFVarIds_624_);
lean_inc(v_mctx_623_);
lean_dec(v___x_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_mctx_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_zetaDeltaFVarIds_624_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_postponed_625_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_diag_626_);
v___x_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_st_ref_set(v_a_590_, v___x_632_);
lean_inc_ref(v_a_591_);
v___x_634_ = l_Lean_enableRealizationsForConst(v_name_596_, v_a_591_, v_a_592_);
return v___x_634_;
}
}
}
}
}
else
{
lean_dec(v_name_596_);
return v___x_603_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_name_596_);
v_a_641_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_601_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_601_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_877_; 
v___x_649_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_650_ = l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(v___x_649_, v_a_591_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_877_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_877_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_877_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v_a_660_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v_a_676_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v_a_696_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v_a_709_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___x_822_; 
lean_inc(v_declName_588_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_655_, 0, v_declName_588_);
v___x_656_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_822_ = lean_unbox(v_a_651_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = l_Lean_trace_profiler;
v___x_824_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_options_594_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v_env_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___f_655_);
lean_del_object(v___x_653_);
lean_dec(v_a_651_);
v___x_825_ = lean_st_ref_get(v_a_592_);
v_env_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc_ref(v_env_826_);
lean_dec(v___x_825_);
v___x_827_ = lean_elab_environment_to_kernel_env(v_env_826_);
v___x_828_ = lean_mk_cases_on(v___x_827_, v_declName_588_);
lean_dec(v_declName_588_);
v___x_829_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_828_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_829_);
v___x_831_ = l_Lean_addDecl(v_a_830_, v___x_824_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v_nextMacroScope_835_; lean_object* v_ngen_836_; lean_object* v_auxDeclNGen_837_; lean_object* v_traceState_838_; lean_object* v_messages_839_; lean_object* v_infoState_840_; lean_object* v_snapshotTasks_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___x_831_);
lean_inc(v_name_596_);
v___x_832_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v___x_832_);
v___x_833_ = lean_st_ref_take(v_a_592_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
v_nextMacroScope_835_ = lean_ctor_get(v___x_833_, 1);
v_ngen_836_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_837_ = lean_ctor_get(v___x_833_, 3);
v_traceState_838_ = lean_ctor_get(v___x_833_, 4);
v_messages_839_ = lean_ctor_get(v___x_833_, 6);
v_infoState_840_ = lean_ctor_get(v___x_833_, 7);
v_snapshotTasks_841_ = lean_ctor_get(v___x_833_, 8);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v___x_833_, 5);
lean_dec(v_unused_868_);
v___x_843_ = v___x_833_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snapshotTasks_841_);
lean_inc(v_infoState_840_);
lean_inc(v_messages_839_);
lean_inc(v_traceState_838_);
lean_inc(v_auxDeclNGen_837_);
lean_inc(v_ngen_836_);
lean_inc(v_nextMacroScope_835_);
lean_inc(v_env_834_);
lean_dec(v___x_833_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
lean_inc(v_name_596_);
v___x_845_ = l_Lean_markAuxRecursor(v_env_834_, v_name_596_);
v___x_846_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 5, v___x_846_);
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_nextMacroScope_835_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_ngen_836_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_auxDeclNGen_837_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_traceState_838_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_866_, 6, v_messages_839_);
lean_ctor_set(v_reuseFailAlloc_866_, 7, v_infoState_840_);
lean_ctor_set(v_reuseFailAlloc_866_, 8, v_snapshotTasks_841_);
v___x_848_ = v_reuseFailAlloc_866_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_mctx_851_; lean_object* v_zetaDeltaFVarIds_852_; lean_object* v_postponed_853_; lean_object* v_diag_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v___x_849_ = lean_st_ref_set(v_a_592_, v___x_848_);
v___x_850_ = lean_st_ref_take(v_a_590_);
v_mctx_851_ = lean_ctor_get(v___x_850_, 0);
v_zetaDeltaFVarIds_852_ = lean_ctor_get(v___x_850_, 2);
v_postponed_853_ = lean_ctor_get(v___x_850_, 3);
v_diag_854_ = lean_ctor_get(v___x_850_, 4);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v___x_850_, 1);
lean_dec(v_unused_865_);
v___x_856_ = v___x_850_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_diag_854_);
lean_inc(v_postponed_853_);
lean_inc(v_zetaDeltaFVarIds_852_);
lean_inc(v_mctx_851_);
lean_dec(v___x_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_mctx_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_zetaDeltaFVarIds_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_postponed_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_diag_854_);
v___x_860_ = v_reuseFailAlloc_863_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_st_ref_set(v_a_590_, v___x_860_);
lean_inc_ref(v_a_591_);
v___x_862_ = l_Lean_enableRealizationsForConst(v_name_596_, v_a_591_, v_a_592_);
return v___x_862_;
}
}
}
}
}
else
{
lean_dec(v_name_596_);
return v___x_831_;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_name_596_);
v_a_869_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_829_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_829_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
goto v___jp_724_;
}
}
else
{
goto v___jp_724_;
}
v___jp_657_:
{
lean_object* v___x_661_; double v___x_662_; double v___x_663_; double v___x_664_; double v___x_665_; double v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v___x_661_ = lean_io_mono_nanos_now();
v___x_662_ = lean_float_of_nat(v___y_659_);
v___x_663_ = lean_float_once(&l_Lean_mkCasesOn___closed__4, &l_Lean_mkCasesOn___closed__4_once, _init_l_Lean_mkCasesOn___closed__4);
v___x_664_ = lean_float_div(v___x_662_, v___x_663_);
v___x_665_ = lean_float_of_nat(v___x_661_);
v___x_666_ = lean_float_div(v___x_665_, v___x_663_);
v___x_667_ = lean_box_float(v___x_664_);
v___x_668_ = lean_box_float(v___x_666_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_a_660_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_unbox(v_a_651_);
lean_dec(v_a_651_);
v___x_672_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v___x_649_, v_hasTrace_595_, v___x_656_, v_options_594_, v___x_671_, v___y_658_, v___f_655_, v___x_670_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_672_;
}
v___jp_673_:
{
lean_object* v___x_678_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_a_676_);
v___x_678_ = v___x_653_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v___y_658_ = v___y_674_;
v___y_659_ = v___y_675_;
v_a_660_ = v___x_678_;
goto v___jp_657_;
}
}
v___jp_680_:
{
if (lean_obj_tag(v___y_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_del_object(v___x_653_);
v_a_684_ = lean_ctor_get(v___y_683_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___y_683_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___y_683_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___y_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 1);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v___y_658_ = v___y_681_;
v___y_659_ = v___y_682_;
v_a_660_ = v___x_689_;
goto v___jp_657_;
}
}
}
else
{
lean_object* v_a_692_; 
v_a_692_ = lean_ctor_get(v___y_683_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___y_683_);
v___y_674_ = v___y_681_;
v___y_675_ = v___y_682_;
v_a_676_ = v_a_692_;
goto v___jp_673_;
}
}
v___jp_693_:
{
lean_object* v___x_697_; double v___x_698_; double v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; 
v___x_697_ = lean_io_get_num_heartbeats();
v___x_698_ = lean_float_of_nat(v___y_694_);
v___x_699_ = lean_float_of_nat(v___x_697_);
v___x_700_ = lean_box_float(v___x_698_);
v___x_701_ = lean_box_float(v___x_699_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_a_696_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_unbox(v_a_651_);
lean_dec(v_a_651_);
v___x_705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v___x_649_, v_hasTrace_595_, v___x_656_, v_options_594_, v___x_704_, v___y_695_, v___f_655_, v___x_703_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_705_;
}
v___jp_706_:
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_a_709_);
v___y_694_ = v___y_707_;
v___y_695_ = v___y_708_;
v_a_696_ = v___x_710_;
goto v___jp_693_;
}
v___jp_711_:
{
if (lean_obj_tag(v___y_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___y_714_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___y_714_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___y_714_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___y_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v___y_694_ = v___y_712_;
v___y_695_ = v___y_713_;
v_a_696_ = v___x_720_;
goto v___jp_693_;
}
}
}
else
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___y_714_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___y_714_);
v___y_707_ = v___y_712_;
v___y_708_ = v___y_713_;
v_a_709_ = v_a_723_;
goto v___jp_706_;
}
}
v___jp_724_:
{
lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_725_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(v_a_592_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = l_Lean_trace_profiler_useHeartbeats;
v___x_728_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_options_594_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_env_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = lean_io_mono_nanos_now();
v___x_730_ = lean_st_ref_get(v_a_592_);
v_env_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_env_731_);
lean_dec(v___x_730_);
v___x_732_ = lean_elab_environment_to_kernel_env(v_env_731_);
v___x_733_ = lean_mk_cases_on(v___x_732_, v_declName_588_);
lean_dec(v_declName_588_);
v___x_734_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_733_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_Lean_addDecl(v_a_735_, v___x_728_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v_nextMacroScope_740_; lean_object* v_ngen_741_; lean_object* v_auxDeclNGen_742_; lean_object* v_traceState_743_; lean_object* v_messages_744_; lean_object* v_infoState_745_; lean_object* v_snapshotTasks_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___x_736_);
lean_inc(v_name_596_);
v___x_737_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v___x_737_);
v___x_738_ = lean_st_ref_take(v_a_592_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
v_nextMacroScope_740_ = lean_ctor_get(v___x_738_, 1);
v_ngen_741_ = lean_ctor_get(v___x_738_, 2);
v_auxDeclNGen_742_ = lean_ctor_get(v___x_738_, 3);
v_traceState_743_ = lean_ctor_get(v___x_738_, 4);
v_messages_744_ = lean_ctor_get(v___x_738_, 6);
v_infoState_745_ = lean_ctor_get(v___x_738_, 7);
v_snapshotTasks_746_ = lean_ctor_get(v___x_738_, 8);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_738_, 5);
lean_dec(v_unused_773_);
v___x_748_ = v___x_738_;
v_isShared_749_ = v_isSharedCheck_772_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snapshotTasks_746_);
lean_inc(v_infoState_745_);
lean_inc(v_messages_744_);
lean_inc(v_traceState_743_);
lean_inc(v_auxDeclNGen_742_);
lean_inc(v_ngen_741_);
lean_inc(v_nextMacroScope_740_);
lean_inc(v_env_739_);
lean_dec(v___x_738_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_772_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_inc(v_name_596_);
v___x_750_ = l_Lean_markAuxRecursor(v_env_739_, v_name_596_);
v___x_751_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 5, v___x_751_);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_753_ = v___x_748_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_nextMacroScope_740_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_ngen_741_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_auxDeclNGen_742_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_traceState_743_);
lean_ctor_set(v_reuseFailAlloc_771_, 5, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_771_, 6, v_messages_744_);
lean_ctor_set(v_reuseFailAlloc_771_, 7, v_infoState_745_);
lean_ctor_set(v_reuseFailAlloc_771_, 8, v_snapshotTasks_746_);
v___x_753_ = v_reuseFailAlloc_771_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_mctx_756_; lean_object* v_zetaDeltaFVarIds_757_; lean_object* v_postponed_758_; lean_object* v_diag_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_769_; 
v___x_754_ = lean_st_ref_set(v_a_592_, v___x_753_);
v___x_755_ = lean_st_ref_take(v_a_590_);
v_mctx_756_ = lean_ctor_get(v___x_755_, 0);
v_zetaDeltaFVarIds_757_ = lean_ctor_get(v___x_755_, 2);
v_postponed_758_ = lean_ctor_get(v___x_755_, 3);
v_diag_759_ = lean_ctor_get(v___x_755_, 4);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_755_, 1);
lean_dec(v_unused_770_);
v___x_761_ = v___x_755_;
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_diag_759_);
lean_inc(v_postponed_758_);
lean_inc(v_zetaDeltaFVarIds_757_);
lean_inc(v_mctx_756_);
lean_dec(v___x_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_mctx_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_zetaDeltaFVarIds_757_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_postponed_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_diag_759_);
v___x_765_ = v_reuseFailAlloc_768_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_st_ref_set(v_a_590_, v___x_765_);
lean_inc_ref(v_a_591_);
v___x_767_ = l_Lean_enableRealizationsForConst(v_name_596_, v_a_591_, v_a_592_);
v___y_681_ = v_a_726_;
v___y_682_ = v___x_729_;
v___y_683_ = v___x_767_;
goto v___jp_680_;
}
}
}
}
}
else
{
lean_dec(v_name_596_);
v___y_681_ = v_a_726_;
v___y_682_ = v___x_729_;
v___y_683_ = v___x_736_;
goto v___jp_680_;
}
}
else
{
lean_object* v_a_774_; 
lean_dec(v_name_596_);
v_a_774_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_734_);
v___y_674_ = v_a_726_;
v___y_675_ = v___x_729_;
v_a_676_ = v_a_774_;
goto v___jp_673_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_env_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_653_);
v___x_775_ = lean_io_get_num_heartbeats();
v___x_776_ = lean_st_ref_get(v_a_592_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc_ref(v_env_777_);
lean_dec(v___x_776_);
v___x_778_ = lean_elab_environment_to_kernel_env(v_env_777_);
v___x_779_ = lean_mk_cases_on(v___x_778_, v_declName_588_);
lean_dec(v_declName_588_);
v___x_780_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_779_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v___x_782_ = 0;
v___x_783_ = l_Lean_addDecl(v_a_781_, v___x_782_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_env_786_; lean_object* v_nextMacroScope_787_; lean_object* v_ngen_788_; lean_object* v_auxDeclNGen_789_; lean_object* v_traceState_790_; lean_object* v_messages_791_; lean_object* v_infoState_792_; lean_object* v_snapshotTasks_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v___x_783_);
lean_inc(v_name_596_);
v___x_784_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v___x_784_);
v___x_785_ = lean_st_ref_take(v_a_592_);
v_env_786_ = lean_ctor_get(v___x_785_, 0);
v_nextMacroScope_787_ = lean_ctor_get(v___x_785_, 1);
v_ngen_788_ = lean_ctor_get(v___x_785_, 2);
v_auxDeclNGen_789_ = lean_ctor_get(v___x_785_, 3);
v_traceState_790_ = lean_ctor_get(v___x_785_, 4);
v_messages_791_ = lean_ctor_get(v___x_785_, 6);
v_infoState_792_ = lean_ctor_get(v___x_785_, 7);
v_snapshotTasks_793_ = lean_ctor_get(v___x_785_, 8);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_785_, 5);
lean_dec(v_unused_820_);
v___x_795_ = v___x_785_;
v_isShared_796_ = v_isSharedCheck_819_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snapshotTasks_793_);
lean_inc(v_infoState_792_);
lean_inc(v_messages_791_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_789_);
lean_inc(v_ngen_788_);
lean_inc(v_nextMacroScope_787_);
lean_inc(v_env_786_);
lean_dec(v___x_785_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_819_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc(v_name_596_);
v___x_797_ = l_Lean_markAuxRecursor(v_env_786_, v_name_596_);
v___x_798_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 5, v___x_798_);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_nextMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_ngen_788_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_auxDeclNGen_789_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_traceState_790_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_messages_791_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_infoState_792_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_snapshotTasks_793_);
v___x_800_ = v_reuseFailAlloc_818_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_mctx_803_; lean_object* v_zetaDeltaFVarIds_804_; lean_object* v_postponed_805_; lean_object* v_diag_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
v___x_801_ = lean_st_ref_set(v_a_592_, v___x_800_);
v___x_802_ = lean_st_ref_take(v_a_590_);
v_mctx_803_ = lean_ctor_get(v___x_802_, 0);
v_zetaDeltaFVarIds_804_ = lean_ctor_get(v___x_802_, 2);
v_postponed_805_ = lean_ctor_get(v___x_802_, 3);
v_diag_806_ = lean_ctor_get(v___x_802_, 4);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_802_, 1);
lean_dec(v_unused_817_);
v___x_808_ = v___x_802_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_diag_806_);
lean_inc(v_postponed_805_);
lean_inc(v_zetaDeltaFVarIds_804_);
lean_inc(v_mctx_803_);
lean_dec(v___x_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_mctx_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_zetaDeltaFVarIds_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_postponed_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_diag_806_);
v___x_812_ = v_reuseFailAlloc_815_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_st_ref_set(v_a_590_, v___x_812_);
lean_inc_ref(v_a_591_);
v___x_814_ = l_Lean_enableRealizationsForConst(v_name_596_, v_a_591_, v_a_592_);
v___y_712_ = v___x_775_;
v___y_713_ = v_a_726_;
v___y_714_ = v___x_814_;
goto v___jp_711_;
}
}
}
}
}
else
{
lean_dec(v_name_596_);
v___y_712_ = v___x_775_;
v___y_713_ = v_a_726_;
v___y_714_ = v___x_783_;
goto v___jp_711_;
}
}
else
{
lean_object* v_a_821_; 
lean_dec(v_name_596_);
v_a_821_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_780_);
v___y_707_ = v___x_775_;
v___y_708_ = v_a_726_;
v_a_709_ = v_a_821_;
goto v___jp_706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_mkCasesOn(v_declName_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object* v_00_u03b1_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_00_u03b1_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(v_00_u03b1_893_, v_x_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_declName_901_, uint8_t v_s_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_901_, v_s_902_, v___y_904_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_declName_909_, lean_object* v_s_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_s_boxed_916_; lean_object* v_res_917_; 
v_s_boxed_916_ = lean_unbox(v_s_910_);
v_res_917_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(v_declName_909_, v_s_boxed_916_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9(lean_object* v_00_u03b1_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_x_919_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___boxed(lean_object* v_00_u03b1_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9(v_00_u03b1_926_, v_x_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg();
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5(v_00_u03b1_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_948_, lean_object* v_ex_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_956_, lean_object* v_ex_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(v_00_u03b1_956_, v_ex_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(v_00_u03b1_972_, v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_1041_ = 0;
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_1043_ = l_Lean_registerTraceClass(v___x_1040_, v___x_1041_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_1045_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CasesOn(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_dec_ref(v___y_186_);
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
lean_dec_ref(v___y_216_);
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
lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_currRecDepth_339_; lean_object* v_maxRecDepth_340_; lean_object* v_ref_341_; lean_object* v_currNamespace_342_; lean_object* v_openDecls_343_; lean_object* v_initHeartbeats_344_; lean_object* v_maxHeartbeats_345_; lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; uint8_t v_diag_348_; lean_object* v_cancelTk_x3f_349_; uint8_t v_suppressElabErrors_350_; lean_object* v_inheritedTraceOptions_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_406_; 
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
v_isSharedCheck_406_ = !lean_is_exclusive(v___y_333_);
if (v_isSharedCheck_406_ == 0)
{
v___x_353_ = v___y_333_;
v_isShared_354_ = v_isSharedCheck_406_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_inheritedTraceOptions_351_);
lean_inc(v_cancelTk_x3f_349_);
lean_inc(v_currMacroScope_347_);
lean_inc(v_quotContext_346_);
lean_inc(v_maxHeartbeats_345_);
lean_inc(v_initHeartbeats_344_);
lean_inc(v_openDecls_343_);
lean_inc(v_currNamespace_342_);
lean_inc(v_ref_341_);
lean_inc(v_maxRecDepth_340_);
lean_inc(v_currRecDepth_339_);
lean_inc(v_options_338_);
lean_inc(v_fileMap_337_);
lean_inc(v_fileName_336_);
lean_dec(v___y_333_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_406_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_traceState_356_; lean_object* v_traces_357_; lean_object* v_ref_358_; lean_object* v___x_360_; 
v___x_355_ = lean_st_ref_get(v___y_334_);
v_traceState_356_ = lean_ctor_get(v___x_355_, 4);
lean_inc_ref(v_traceState_356_);
lean_dec(v___x_355_);
v_traces_357_ = lean_ctor_get(v_traceState_356_, 0);
lean_inc_ref(v_traces_357_);
lean_dec_ref(v_traceState_356_);
v_ref_358_ = l_Lean_replaceRef(v_ref_329_, v_ref_341_);
lean_dec(v_ref_341_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 5, v_ref_358_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fileName_336_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_fileMap_337_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_options_338_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_currRecDepth_339_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_maxRecDepth_340_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_ref_358_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_currNamespace_342_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_openDecls_343_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_initHeartbeats_344_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_maxHeartbeats_345_);
lean_ctor_set(v_reuseFailAlloc_405_, 10, v_quotContext_346_);
lean_ctor_set(v_reuseFailAlloc_405_, 11, v_currMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_405_, 12, v_cancelTk_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_405_, 13, v_inheritedTraceOptions_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*14, v_diag_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*14 + 1, v_suppressElabErrors_350_);
v___x_360_ = v_reuseFailAlloc_405_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; size_t v_sz_362_; size_t v___x_363_; lean_object* v___x_364_; lean_object* v_msg_365_; lean_object* v___x_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_404_; 
v___x_361_ = l_Lean_PersistentArray_toArray___redArg(v_traces_357_);
lean_dec_ref(v_traces_357_);
v_sz_362_ = lean_array_size(v___x_361_);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__11(v_sz_362_, v___x_363_, v___x_361_);
v_msg_365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_365_, 0, v_data_328_);
lean_ctor_set(v_msg_365_, 1, v_msg_330_);
lean_ctor_set(v_msg_365_, 2, v___x_364_);
v___x_366_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8_spec__12(v_msg_365_, v___y_331_, v___y_332_, v___x_360_, v___y_334_);
lean_dec_ref(v___x_360_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_404_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_404_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_404_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v_traceState_372_; lean_object* v_env_373_; lean_object* v_nextMacroScope_374_; lean_object* v_ngen_375_; lean_object* v_auxDeclNGen_376_; lean_object* v_cache_377_; lean_object* v_messages_378_; lean_object* v_infoState_379_; lean_object* v_snapshotTasks_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_403_; 
v___x_371_ = lean_st_ref_take(v___y_334_);
v_traceState_372_ = lean_ctor_get(v___x_371_, 4);
v_env_373_ = lean_ctor_get(v___x_371_, 0);
v_nextMacroScope_374_ = lean_ctor_get(v___x_371_, 1);
v_ngen_375_ = lean_ctor_get(v___x_371_, 2);
v_auxDeclNGen_376_ = lean_ctor_get(v___x_371_, 3);
v_cache_377_ = lean_ctor_get(v___x_371_, 5);
v_messages_378_ = lean_ctor_get(v___x_371_, 6);
v_infoState_379_ = lean_ctor_get(v___x_371_, 7);
v_snapshotTasks_380_ = lean_ctor_get(v___x_371_, 8);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_403_ == 0)
{
v___x_382_ = v___x_371_;
v_isShared_383_ = v_isSharedCheck_403_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snapshotTasks_380_);
lean_inc(v_infoState_379_);
lean_inc(v_messages_378_);
lean_inc(v_cache_377_);
lean_inc(v_traceState_372_);
lean_inc(v_auxDeclNGen_376_);
lean_inc(v_ngen_375_);
lean_inc(v_nextMacroScope_374_);
lean_inc(v_env_373_);
lean_dec(v___x_371_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_403_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint64_t v_tid_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_401_; 
v_tid_384_ = lean_ctor_get_uint64(v_traceState_372_, sizeof(void*)*1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_traceState_372_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_traceState_372_, 0);
lean_dec(v_unused_402_);
v___x_386_ = v_traceState_372_;
v_isShared_387_ = v_isSharedCheck_401_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_traceState_372_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_401_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_ref_329_);
lean_ctor_set(v___x_388_, 1, v_a_367_);
v___x_389_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_327_, v___x_388_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_389_);
lean_ctor_set_uint64(v_reuseFailAlloc_400_, sizeof(void*)*1, v_tid_384_);
v___x_391_ = v_reuseFailAlloc_400_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 4, v___x_391_);
v___x_393_ = v___x_382_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_env_373_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_374_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_messages_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_infoState_379_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_snapshotTasks_380_);
v___x_393_ = v_reuseFailAlloc_399_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_st_ref_set(v___y_334_, v___x_393_);
v___x_395_ = lean_box(0);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_395_);
v___x_397_ = v___x_369_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8___boxed(lean_object* v_oldTraces_407_, lean_object* v_data_408_, lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(v_oldTraces_407_, v_data_408_, v_ref_409_, v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(lean_object* v_opts_417_, lean_object* v_opt_418_){
_start:
{
lean_object* v_name_419_; lean_object* v_defValue_420_; lean_object* v_map_421_; lean_object* v___x_422_; 
v_name_419_ = lean_ctor_get(v_opt_418_, 0);
v_defValue_420_ = lean_ctor_get(v_opt_418_, 1);
v_map_421_ = lean_ctor_get(v_opts_417_, 0);
v___x_422_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_421_, v_name_419_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_inc(v_defValue_420_);
return v_defValue_420_;
}
else
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref(v___x_422_);
if (lean_obj_tag(v_val_423_) == 3)
{
lean_object* v_v_424_; 
v_v_424_ = lean_ctor_get(v_val_423_, 0);
lean_inc(v_v_424_);
lean_dec_ref(v_val_423_);
return v_v_424_;
}
else
{
lean_dec(v_val_423_);
lean_inc(v_defValue_420_);
return v_defValue_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10___boxed(lean_object* v_opts_425_, lean_object* v_opt_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_425_, v_opt_426_);
lean_dec_ref(v_opt_426_);
lean_dec_ref(v_opts_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v_x_428_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v_x_428_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v_x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 1);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v_x_428_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v_x_428_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_428_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 0);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg___boxed(lean_object* v_x_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_x_446_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(lean_object* v_e_449_){
_start:
{
if (lean_obj_tag(v_e_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 2;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 0;
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7___boxed(lean_object* v_e_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(v_e_452_);
lean_dec_ref(v_e_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__3));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5(void){
_start:
{
lean_object* v___x_463_; double v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(1000u);
v___x_464_ = lean_float_of_nat(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(lean_object* v_cls_465_, uint8_t v_collapsed_466_, lean_object* v_tag_467_, lean_object* v_opts_468_, uint8_t v_clsEnabled_469_, lean_object* v_oldTraces_470_, lean_object* v_msg_471_, lean_object* v_resStartStop_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_569_; 
v_fst_478_ = lean_ctor_get(v_resStartStop_472_, 0);
v_snd_479_ = lean_ctor_get(v_resStartStop_472_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_resStartStop_472_);
if (v_isSharedCheck_569_ == 0)
{
v___x_481_ = v_resStartStop_472_;
v_isShared_482_ = v_isSharedCheck_569_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_inc(v_fst_478_);
lean_dec(v_resStartStop_472_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_569_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v_data_486_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_568_; 
v_fst_489_ = lean_ctor_get(v_snd_479_, 0);
v_snd_490_ = lean_ctor_get(v_snd_479_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_snd_479_);
if (v_isSharedCheck_568_ == 0)
{
v___x_492_ = v_snd_479_;
v_isShared_493_ = v_isSharedCheck_568_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_snd_479_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_568_;
goto v_resetjp_491_;
}
v___jp_483_:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__8(v_oldTraces_470_, v_data_486_, v___y_485_, v___y_484_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v___x_487_);
v___x_488_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_fst_478_);
return v___x_488_;
}
else
{
lean_dec(v_fst_478_);
return v___x_487_;
}
}
v_resetjp_491_:
{
lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___y_497_; lean_object* v_a_498_; uint8_t v___y_522_; double v___y_553_; 
v___x_494_ = l_Lean_trace_profiler;
v___x_495_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_opts_468_, v___x_494_);
if (v___x_495_ == 0)
{
v___y_522_ = v___x_495_;
goto v___jp_521_;
}
else
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = l_Lean_trace_profiler_useHeartbeats;
v___x_559_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_opts_468_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; double v___x_562_; double v___x_563_; double v___x_564_; 
v___x_560_ = l_Lean_trace_profiler_threshold;
v___x_561_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_468_, v___x_560_);
v___x_562_ = lean_float_of_nat(v___x_561_);
v___x_563_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__5);
v___x_564_ = lean_float_div(v___x_562_, v___x_563_);
v___y_553_ = v___x_564_;
goto v___jp_552_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; double v___x_567_; 
v___x_565_ = l_Lean_trace_profiler_threshold;
v___x_566_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__10(v_opts_468_, v___x_565_);
v___x_567_ = lean_float_of_nat(v___x_566_);
v___y_553_ = v___x_567_;
goto v___jp_552_;
}
}
v___jp_496_:
{
uint8_t v_result_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v_result_499_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__7(v_fst_478_);
v___x_500_ = l_Lean_TraceResult_toEmoji(v_result_499_);
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__1);
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 7);
lean_ctor_set(v___x_492_, 1, v___x_502_);
lean_ctor_set(v___x_492_, 0, v___x_501_);
v___x_504_ = v___x_492_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_515_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v_m_506_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 7);
lean_ctor_set(v___x_481_, 1, v_a_498_);
lean_ctor_set(v___x_481_, 0, v___x_504_);
v_m_506_ = v___x_481_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_a_498_);
v_m_506_ = v_reuseFailAlloc_514_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; double v___x_509_; lean_object* v_data_510_; 
v___x_507_ = lean_box(v_result_499_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__2);
lean_inc_ref(v_tag_467_);
lean_inc_ref(v___x_508_);
lean_inc(v_cls_465_);
v_data_510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_510_, 0, v_cls_465_);
lean_ctor_set(v_data_510_, 1, v___x_508_);
lean_ctor_set(v_data_510_, 2, v_tag_467_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3, v___x_509_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3 + 8, v___x_509_);
lean_ctor_set_uint8(v_data_510_, sizeof(void*)*3 + 16, v_collapsed_466_);
if (v___x_495_ == 0)
{
lean_dec_ref(v___x_508_);
lean_dec(v_snd_490_);
lean_dec(v_fst_489_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___y_484_ = v_m_506_;
v___y_485_ = v___y_497_;
v_data_486_ = v_data_510_;
goto v___jp_483_;
}
else
{
lean_object* v_data_511_; double v___x_512_; double v___x_513_; 
lean_dec_ref(v_data_510_);
v_data_511_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_511_, 0, v_cls_465_);
lean_ctor_set(v_data_511_, 1, v___x_508_);
lean_ctor_set(v_data_511_, 2, v_tag_467_);
v___x_512_ = lean_unbox_float(v_fst_489_);
lean_dec(v_fst_489_);
lean_ctor_set_float(v_data_511_, sizeof(void*)*3, v___x_512_);
v___x_513_ = lean_unbox_float(v_snd_490_);
lean_dec(v_snd_490_);
lean_ctor_set_float(v_data_511_, sizeof(void*)*3 + 8, v___x_513_);
lean_ctor_set_uint8(v_data_511_, sizeof(void*)*3 + 16, v_collapsed_466_);
v___y_484_ = v_m_506_;
v___y_485_ = v___y_497_;
v_data_486_ = v_data_511_;
goto v___jp_483_;
}
}
}
}
v___jp_516_:
{
lean_object* v_ref_517_; lean_object* v___x_518_; 
v_ref_517_ = lean_ctor_get(v___y_475_, 5);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v_fst_478_);
v___x_518_ = lean_apply_6(v_msg_471_, v_fst_478_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref(v___x_518_);
lean_inc(v_ref_517_);
v___y_497_ = v_ref_517_;
v_a_498_ = v_a_519_;
goto v___jp_496_;
}
else
{
lean_object* v___x_520_; 
lean_dec_ref(v___x_518_);
v___x_520_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___closed__4);
lean_inc(v_ref_517_);
v___y_497_ = v_ref_517_;
v_a_498_ = v___x_520_;
goto v___jp_496_;
}
}
v___jp_521_:
{
if (v_clsEnabled_469_ == 0)
{
if (v___y_522_ == 0)
{
lean_object* v___x_523_; lean_object* v_traceState_524_; lean_object* v_env_525_; lean_object* v_nextMacroScope_526_; lean_object* v_ngen_527_; lean_object* v_auxDeclNGen_528_; lean_object* v_cache_529_; lean_object* v_messages_530_; lean_object* v_infoState_531_; lean_object* v_snapshotTasks_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_492_);
lean_dec(v_snd_490_);
lean_dec(v_fst_489_);
lean_del_object(v___x_481_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec_ref(v_msg_471_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___x_523_ = lean_st_ref_take(v___y_476_);
v_traceState_524_ = lean_ctor_get(v___x_523_, 4);
v_env_525_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_526_ = lean_ctor_get(v___x_523_, 1);
v_ngen_527_ = lean_ctor_get(v___x_523_, 2);
v_auxDeclNGen_528_ = lean_ctor_get(v___x_523_, 3);
v_cache_529_ = lean_ctor_get(v___x_523_, 5);
v_messages_530_ = lean_ctor_get(v___x_523_, 6);
v_infoState_531_ = lean_ctor_get(v___x_523_, 7);
v_snapshotTasks_532_ = lean_ctor_get(v___x_523_, 8);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_551_ == 0)
{
v___x_534_ = v___x_523_;
v_isShared_535_ = v_isSharedCheck_551_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snapshotTasks_532_);
lean_inc(v_infoState_531_);
lean_inc(v_messages_530_);
lean_inc(v_cache_529_);
lean_inc(v_traceState_524_);
lean_inc(v_auxDeclNGen_528_);
lean_inc(v_ngen_527_);
lean_inc(v_nextMacroScope_526_);
lean_inc(v_env_525_);
lean_dec(v___x_523_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_551_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint64_t v_tid_536_; lean_object* v_traces_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_550_; 
v_tid_536_ = lean_ctor_get_uint64(v_traceState_524_, sizeof(void*)*1);
v_traces_537_ = lean_ctor_get(v_traceState_524_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_traceState_524_);
if (v_isSharedCheck_550_ == 0)
{
v___x_539_ = v_traceState_524_;
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_traces_537_);
lean_dec(v_traceState_524_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_470_, v_traces_537_);
lean_dec_ref(v_traces_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_541_);
lean_ctor_set_uint64(v_reuseFailAlloc_549_, sizeof(void*)*1, v_tid_536_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 4, v___x_543_);
v___x_545_ = v___x_534_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_env_525_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_nextMacroScope_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_ngen_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_auxDeclNGen_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_cache_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_messages_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_infoState_531_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v_snapshotTasks_532_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_st_ref_set(v___y_476_, v___x_545_);
lean_dec(v___y_476_);
v___x_547_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_fst_478_);
return v___x_547_;
}
}
}
}
}
else
{
goto v___jp_516_;
}
}
else
{
goto v___jp_516_;
}
}
v___jp_552_:
{
double v___x_554_; double v___x_555_; double v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_unbox_float(v_snd_490_);
v___x_555_ = lean_unbox_float(v_fst_489_);
v___x_556_ = lean_float_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_float_decLt(v___y_553_, v___x_556_);
v___y_522_ = v___x_557_;
goto v___jp_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5___boxed(lean_object* v_cls_570_, lean_object* v_collapsed_571_, lean_object* v_tag_572_, lean_object* v_opts_573_, lean_object* v_clsEnabled_574_, lean_object* v_oldTraces_575_, lean_object* v_msg_576_, lean_object* v_resStartStop_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_collapsed_boxed_583_; uint8_t v_clsEnabled_boxed_584_; lean_object* v_res_585_; 
v_collapsed_boxed_583_ = lean_unbox(v_collapsed_571_);
v_clsEnabled_boxed_584_ = lean_unbox(v_clsEnabled_574_);
v_res_585_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v_cls_570_, v_collapsed_boxed_583_, v_tag_572_, v_opts_573_, v_clsEnabled_boxed_584_, v_oldTraces_575_, v_msg_576_, v_resStartStop_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_opts_573_);
return v_res_585_;
}
}
static double _init_l_Lean_mkCasesOn___closed__4(void){
_start:
{
lean_object* v___x_592_; double v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1000000000u);
v___x_593_ = lean_float_of_nat(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_options_600_; uint8_t v_hasTrace_601_; lean_object* v_name_602_; 
v_options_600_ = lean_ctor_get(v_a_597_, 2);
v_hasTrace_601_ = lean_ctor_get_uint8(v_options_600_, sizeof(void*)*1);
lean_inc(v_declName_594_);
v_name_602_ = l_Lean_mkCasesOnName(v_declName_594_);
if (v_hasTrace_601_ == 0)
{
lean_object* v___x_603_; lean_object* v_env_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_603_ = lean_st_ref_get(v_a_598_);
v_env_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc_ref(v_env_604_);
lean_dec(v___x_603_);
v___x_605_ = lean_elab_environment_to_kernel_env(v_env_604_);
v___x_606_ = lean_mk_cases_on(v___x_605_, v_declName_594_);
lean_dec(v_declName_594_);
lean_inc_ref(v_a_597_);
v___x_607_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_606_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_609_ = l_Lean_addDecl(v_a_608_, v_hasTrace_601_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v_nextMacroScope_613_; lean_object* v_ngen_614_; lean_object* v_auxDeclNGen_615_; lean_object* v_traceState_616_; lean_object* v_messages_617_; lean_object* v_infoState_618_; lean_object* v_snapshotTasks_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v___x_609_);
lean_inc(v_name_602_);
v___x_610_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_602_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_a_595_);
lean_dec_ref(v___x_610_);
v___x_611_ = lean_st_ref_take(v_a_598_);
v_env_612_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_613_ = lean_ctor_get(v___x_611_, 1);
v_ngen_614_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_615_ = lean_ctor_get(v___x_611_, 3);
v_traceState_616_ = lean_ctor_get(v___x_611_, 4);
v_messages_617_ = lean_ctor_get(v___x_611_, 6);
v_infoState_618_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_619_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_611_, 5);
lean_dec(v_unused_646_);
v___x_621_ = v___x_611_;
v_isShared_622_ = v_isSharedCheck_645_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snapshotTasks_619_);
lean_inc(v_infoState_618_);
lean_inc(v_messages_617_);
lean_inc(v_traceState_616_);
lean_inc(v_auxDeclNGen_615_);
lean_inc(v_ngen_614_);
lean_inc(v_nextMacroScope_613_);
lean_inc(v_env_612_);
lean_dec(v___x_611_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_645_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_inc(v_name_602_);
v___x_623_ = l_Lean_markAuxRecursor(v_env_612_, v_name_602_);
v___x_624_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 5, v___x_624_);
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_nextMacroScope_613_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_ngen_614_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_auxDeclNGen_615_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_traceState_616_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_644_, 6, v_messages_617_);
lean_ctor_set(v_reuseFailAlloc_644_, 7, v_infoState_618_);
lean_ctor_set(v_reuseFailAlloc_644_, 8, v_snapshotTasks_619_);
v___x_626_ = v_reuseFailAlloc_644_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_mctx_629_; lean_object* v_zetaDeltaFVarIds_630_; lean_object* v_postponed_631_; lean_object* v_diag_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
v___x_627_ = lean_st_ref_set(v_a_598_, v___x_626_);
v___x_628_ = lean_st_ref_take(v_a_596_);
v_mctx_629_ = lean_ctor_get(v___x_628_, 0);
v_zetaDeltaFVarIds_630_ = lean_ctor_get(v___x_628_, 2);
v_postponed_631_ = lean_ctor_get(v___x_628_, 3);
v_diag_632_ = lean_ctor_get(v___x_628_, 4);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_628_, 1);
lean_dec(v_unused_643_);
v___x_634_ = v___x_628_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_diag_632_);
lean_inc(v_postponed_631_);
lean_inc(v_zetaDeltaFVarIds_630_);
lean_inc(v_mctx_629_);
lean_dec(v___x_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_mctx_629_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_zetaDeltaFVarIds_630_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_postponed_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_diag_632_);
v___x_638_ = v_reuseFailAlloc_641_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_st_ref_set(v_a_596_, v___x_638_);
lean_dec(v_a_596_);
v___x_640_ = l_Lean_enableRealizationsForConst(v_name_602_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
return v___x_640_;
}
}
}
}
}
else
{
lean_dec(v_name_602_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v___x_609_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_name_602_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
v_a_647_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_607_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_607_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_883_; 
v___x_655_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_656_ = l_Lean_isTracingEnabledFor___at___00Lean_mkCasesOn_spec__2___redArg(v___x_655_, v_a_597_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_883_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_883_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_883_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___f_661_; lean_object* v___x_662_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v_a_666_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v_a_682_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_a_702_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v_a_715_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___x_828_; 
lean_inc(v_declName_594_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_661_, 0, v_declName_594_);
v___x_662_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_828_ = lean_unbox(v_a_657_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_trace_profiler;
v___x_830_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_options_600_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v_env_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v___f_661_);
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
v___x_831_ = lean_st_ref_get(v_a_598_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = lean_elab_environment_to_kernel_env(v_env_832_);
v___x_834_ = lean_mk_cases_on(v___x_833_, v_declName_594_);
lean_dec(v_declName_594_);
lean_inc_ref(v_a_597_);
v___x_835_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_834_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_835_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_837_ = l_Lean_addDecl(v_a_836_, v___x_830_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_env_840_; lean_object* v_nextMacroScope_841_; lean_object* v_ngen_842_; lean_object* v_auxDeclNGen_843_; lean_object* v_traceState_844_; lean_object* v_messages_845_; lean_object* v_infoState_846_; lean_object* v_snapshotTasks_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___x_837_);
lean_inc(v_name_602_);
v___x_838_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_602_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_a_595_);
lean_dec_ref(v___x_838_);
v___x_839_ = lean_st_ref_take(v_a_598_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
v_nextMacroScope_841_ = lean_ctor_get(v___x_839_, 1);
v_ngen_842_ = lean_ctor_get(v___x_839_, 2);
v_auxDeclNGen_843_ = lean_ctor_get(v___x_839_, 3);
v_traceState_844_ = lean_ctor_get(v___x_839_, 4);
v_messages_845_ = lean_ctor_get(v___x_839_, 6);
v_infoState_846_ = lean_ctor_get(v___x_839_, 7);
v_snapshotTasks_847_ = lean_ctor_get(v___x_839_, 8);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_839_, 5);
lean_dec(v_unused_874_);
v___x_849_ = v___x_839_;
v_isShared_850_ = v_isSharedCheck_873_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snapshotTasks_847_);
lean_inc(v_infoState_846_);
lean_inc(v_messages_845_);
lean_inc(v_traceState_844_);
lean_inc(v_auxDeclNGen_843_);
lean_inc(v_ngen_842_);
lean_inc(v_nextMacroScope_841_);
lean_inc(v_env_840_);
lean_dec(v___x_839_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_873_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
lean_inc(v_name_602_);
v___x_851_ = l_Lean_markAuxRecursor(v_env_840_, v_name_602_);
v___x_852_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 5, v___x_852_);
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_nextMacroScope_841_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_ngen_842_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_auxDeclNGen_843_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_traceState_844_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_872_, 6, v_messages_845_);
lean_ctor_set(v_reuseFailAlloc_872_, 7, v_infoState_846_);
lean_ctor_set(v_reuseFailAlloc_872_, 8, v_snapshotTasks_847_);
v___x_854_ = v_reuseFailAlloc_872_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_mctx_857_; lean_object* v_zetaDeltaFVarIds_858_; lean_object* v_postponed_859_; lean_object* v_diag_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_870_; 
v___x_855_ = lean_st_ref_set(v_a_598_, v___x_854_);
v___x_856_ = lean_st_ref_take(v_a_596_);
v_mctx_857_ = lean_ctor_get(v___x_856_, 0);
v_zetaDeltaFVarIds_858_ = lean_ctor_get(v___x_856_, 2);
v_postponed_859_ = lean_ctor_get(v___x_856_, 3);
v_diag_860_ = lean_ctor_get(v___x_856_, 4);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_856_, 1);
lean_dec(v_unused_871_);
v___x_862_ = v___x_856_;
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_diag_860_);
lean_inc(v_postponed_859_);
lean_inc(v_zetaDeltaFVarIds_858_);
lean_inc(v_mctx_857_);
lean_dec(v___x_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_mctx_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_zetaDeltaFVarIds_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_postponed_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_diag_860_);
v___x_866_ = v_reuseFailAlloc_869_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_st_ref_set(v_a_596_, v___x_866_);
lean_dec(v_a_596_);
v___x_868_ = l_Lean_enableRealizationsForConst(v_name_602_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
return v___x_868_;
}
}
}
}
}
else
{
lean_dec(v_name_602_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v___x_837_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_name_602_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
v_a_875_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_835_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_835_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_inc_ref(v_options_600_);
goto v___jp_730_;
}
}
else
{
lean_inc_ref(v_options_600_);
goto v___jp_730_;
}
v___jp_663_:
{
lean_object* v___x_667_; double v___x_668_; double v___x_669_; double v___x_670_; double v___x_671_; double v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_667_ = lean_io_mono_nanos_now();
v___x_668_ = lean_float_of_nat(v___y_665_);
v___x_669_ = lean_float_once(&l_Lean_mkCasesOn___closed__4, &l_Lean_mkCasesOn___closed__4_once, _init_l_Lean_mkCasesOn___closed__4);
v___x_670_ = lean_float_div(v___x_668_, v___x_669_);
v___x_671_ = lean_float_of_nat(v___x_667_);
v___x_672_ = lean_float_div(v___x_671_, v___x_669_);
v___x_673_ = lean_box_float(v___x_670_);
v___x_674_ = lean_box_float(v___x_672_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_a_666_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
v___x_678_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v___x_655_, v_hasTrace_601_, v___x_662_, v_options_600_, v___x_677_, v___y_664_, v___f_661_, v___x_676_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_options_600_);
return v___x_678_;
}
v___jp_679_:
{
lean_object* v___x_684_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_a_682_);
v___x_684_ = v___x_659_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v___y_664_ = v___y_680_;
v___y_665_ = v___y_681_;
v_a_666_ = v___x_684_;
goto v___jp_663_;
}
}
v___jp_686_:
{
if (lean_obj_tag(v___y_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_del_object(v___x_659_);
v_a_690_ = lean_ctor_get(v___y_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___y_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___y_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___y_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v___y_664_ = v___y_687_;
v___y_665_ = v___y_688_;
v_a_666_ = v___x_695_;
goto v___jp_663_;
}
}
}
else
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___y_689_);
v___y_680_ = v___y_687_;
v___y_681_ = v___y_688_;
v_a_682_ = v_a_698_;
goto v___jp_679_;
}
}
v___jp_699_:
{
lean_object* v___x_703_; double v___x_704_; double v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; 
v___x_703_ = lean_io_get_num_heartbeats();
v___x_704_ = lean_float_of_nat(v___y_701_);
v___x_705_ = lean_float_of_nat(v___x_703_);
v___x_706_ = lean_box_float(v___x_704_);
v___x_707_ = lean_box_float(v___x_705_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_a_702_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
v___x_711_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5(v___x_655_, v_hasTrace_601_, v___x_662_, v_options_600_, v___x_710_, v___y_700_, v___f_661_, v___x_709_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_options_600_);
return v___x_711_;
}
v___jp_712_:
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_a_715_);
v___y_700_ = v___y_713_;
v___y_701_ = v___y_714_;
v_a_702_ = v___x_716_;
goto v___jp_699_;
}
v___jp_717_:
{
if (lean_obj_tag(v___y_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___y_720_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___y_720_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___y_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 1);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
v___y_700_ = v___y_718_;
v___y_701_ = v___y_719_;
v_a_702_ = v___x_726_;
goto v___jp_699_;
}
}
}
else
{
lean_object* v_a_729_; 
v_a_729_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___y_720_);
v___y_713_ = v___y_718_;
v___y_714_ = v___y_719_;
v_a_715_ = v_a_729_;
goto v___jp_712_;
}
}
v___jp_730_:
{
lean_object* v___x_731_; lean_object* v_a_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_731_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__3___redArg(v_a_598_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = l_Lean_trace_profiler_useHeartbeats;
v___x_734_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__4(v_options_600_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_env_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_735_ = lean_io_mono_nanos_now();
v___x_736_ = lean_st_ref_get(v_a_598_);
v_env_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc_ref(v_env_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_elab_environment_to_kernel_env(v_env_737_);
v___x_739_ = lean_mk_cases_on(v___x_738_, v_declName_594_);
lean_dec(v_declName_594_);
lean_inc_ref(v_a_597_);
v___x_740_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_739_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_740_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_742_ = l_Lean_addDecl(v_a_741_, v___x_734_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_env_745_; lean_object* v_nextMacroScope_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_traceState_749_; lean_object* v_messages_750_; lean_object* v_infoState_751_; lean_object* v_snapshotTasks_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___x_742_);
lean_inc(v_name_602_);
v___x_743_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_602_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v___x_743_);
v___x_744_ = lean_st_ref_take(v_a_598_);
v_env_745_ = lean_ctor_get(v___x_744_, 0);
v_nextMacroScope_746_ = lean_ctor_get(v___x_744_, 1);
v_ngen_747_ = lean_ctor_get(v___x_744_, 2);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_744_, 3);
v_traceState_749_ = lean_ctor_get(v___x_744_, 4);
v_messages_750_ = lean_ctor_get(v___x_744_, 6);
v_infoState_751_ = lean_ctor_get(v___x_744_, 7);
v_snapshotTasks_752_ = lean_ctor_get(v___x_744_, 8);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_744_, 5);
lean_dec(v_unused_779_);
v___x_754_ = v___x_744_;
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snapshotTasks_752_);
lean_inc(v_infoState_751_);
lean_inc(v_messages_750_);
lean_inc(v_traceState_749_);
lean_inc(v_auxDeclNGen_748_);
lean_inc(v_ngen_747_);
lean_inc(v_nextMacroScope_746_);
lean_inc(v_env_745_);
lean_dec(v___x_744_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_inc(v_name_602_);
v___x_756_ = l_Lean_markAuxRecursor(v_env_745_, v_name_602_);
v___x_757_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 5, v___x_757_);
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_nextMacroScope_746_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_ngen_747_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_auxDeclNGen_748_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_traceState_749_);
lean_ctor_set(v_reuseFailAlloc_777_, 5, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_777_, 6, v_messages_750_);
lean_ctor_set(v_reuseFailAlloc_777_, 7, v_infoState_751_);
lean_ctor_set(v_reuseFailAlloc_777_, 8, v_snapshotTasks_752_);
v___x_759_ = v_reuseFailAlloc_777_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_mctx_762_; lean_object* v_zetaDeltaFVarIds_763_; lean_object* v_postponed_764_; lean_object* v_diag_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v___x_760_ = lean_st_ref_set(v_a_598_, v___x_759_);
v___x_761_ = lean_st_ref_take(v_a_596_);
v_mctx_762_ = lean_ctor_get(v___x_761_, 0);
v_zetaDeltaFVarIds_763_ = lean_ctor_get(v___x_761_, 2);
v_postponed_764_ = lean_ctor_get(v___x_761_, 3);
v_diag_765_ = lean_ctor_get(v___x_761_, 4);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_761_, 1);
lean_dec(v_unused_776_);
v___x_767_ = v___x_761_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_diag_765_);
lean_inc(v_postponed_764_);
lean_inc(v_zetaDeltaFVarIds_763_);
lean_inc(v_mctx_762_);
lean_dec(v___x_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_mctx_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_zetaDeltaFVarIds_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_postponed_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_diag_765_);
v___x_771_ = v_reuseFailAlloc_774_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_st_ref_set(v_a_596_, v___x_771_);
lean_inc_ref(v_a_597_);
v___x_773_ = l_Lean_enableRealizationsForConst(v_name_602_, v_a_597_, v_a_598_);
v___y_687_ = v_a_732_;
v___y_688_ = v___x_735_;
v___y_689_ = v___x_773_;
goto v___jp_686_;
}
}
}
}
}
else
{
lean_dec(v_name_602_);
v___y_687_ = v_a_732_;
v___y_688_ = v___x_735_;
v___y_689_ = v___x_742_;
goto v___jp_686_;
}
}
else
{
lean_object* v_a_780_; 
lean_dec(v_name_602_);
v_a_780_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_740_);
v___y_680_ = v_a_732_;
v___y_681_ = v___x_735_;
v_a_682_ = v_a_780_;
goto v___jp_679_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_env_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_659_);
v___x_781_ = lean_io_get_num_heartbeats();
v___x_782_ = lean_st_ref_get(v_a_598_);
v_env_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_783_);
lean_dec(v___x_782_);
v___x_784_ = lean_elab_environment_to_kernel_env(v_env_783_);
v___x_785_ = lean_mk_cases_on(v___x_784_, v_declName_594_);
lean_dec(v_declName_594_);
lean_inc_ref(v_a_597_);
v___x_786_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_785_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; uint8_t v___x_788_; lean_object* v___x_789_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
v___x_788_ = 0;
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_789_ = l_Lean_addDecl(v_a_787_, v___x_788_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_env_792_; lean_object* v_nextMacroScope_793_; lean_object* v_ngen_794_; lean_object* v_auxDeclNGen_795_; lean_object* v_traceState_796_; lean_object* v_messages_797_; lean_object* v_infoState_798_; lean_object* v_snapshotTasks_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v___x_789_);
lean_inc(v_name_602_);
v___x_790_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_602_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v___x_790_);
v___x_791_ = lean_st_ref_take(v_a_598_);
v_env_792_ = lean_ctor_get(v___x_791_, 0);
v_nextMacroScope_793_ = lean_ctor_get(v___x_791_, 1);
v_ngen_794_ = lean_ctor_get(v___x_791_, 2);
v_auxDeclNGen_795_ = lean_ctor_get(v___x_791_, 3);
v_traceState_796_ = lean_ctor_get(v___x_791_, 4);
v_messages_797_ = lean_ctor_get(v___x_791_, 6);
v_infoState_798_ = lean_ctor_get(v___x_791_, 7);
v_snapshotTasks_799_ = lean_ctor_get(v___x_791_, 8);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_791_, 5);
lean_dec(v_unused_826_);
v___x_801_ = v___x_791_;
v_isShared_802_ = v_isSharedCheck_825_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_snapshotTasks_799_);
lean_inc(v_infoState_798_);
lean_inc(v_messages_797_);
lean_inc(v_traceState_796_);
lean_inc(v_auxDeclNGen_795_);
lean_inc(v_ngen_794_);
lean_inc(v_nextMacroScope_793_);
lean_inc(v_env_792_);
lean_dec(v___x_791_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_825_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_name_602_);
v___x_803_ = l_Lean_markAuxRecursor(v_env_792_, v_name_602_);
v___x_804_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 5, v___x_804_);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_nextMacroScope_793_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_ngen_794_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_auxDeclNGen_795_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_traceState_796_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_messages_797_);
lean_ctor_set(v_reuseFailAlloc_824_, 7, v_infoState_798_);
lean_ctor_set(v_reuseFailAlloc_824_, 8, v_snapshotTasks_799_);
v___x_806_ = v_reuseFailAlloc_824_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_mctx_809_; lean_object* v_zetaDeltaFVarIds_810_; lean_object* v_postponed_811_; lean_object* v_diag_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
v___x_807_ = lean_st_ref_set(v_a_598_, v___x_806_);
v___x_808_ = lean_st_ref_take(v_a_596_);
v_mctx_809_ = lean_ctor_get(v___x_808_, 0);
v_zetaDeltaFVarIds_810_ = lean_ctor_get(v___x_808_, 2);
v_postponed_811_ = lean_ctor_get(v___x_808_, 3);
v_diag_812_ = lean_ctor_get(v___x_808_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_808_, 1);
lean_dec(v_unused_823_);
v___x_814_ = v___x_808_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_diag_812_);
lean_inc(v_postponed_811_);
lean_inc(v_zetaDeltaFVarIds_810_);
lean_inc(v_mctx_809_);
lean_dec(v___x_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_mctx_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_zetaDeltaFVarIds_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_postponed_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_diag_812_);
v___x_818_ = v_reuseFailAlloc_821_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_st_ref_set(v_a_596_, v___x_818_);
lean_inc_ref(v_a_597_);
v___x_820_ = l_Lean_enableRealizationsForConst(v_name_602_, v_a_597_, v_a_598_);
v___y_718_ = v_a_732_;
v___y_719_ = v___x_781_;
v___y_720_ = v___x_820_;
goto v___jp_717_;
}
}
}
}
}
else
{
lean_dec(v_name_602_);
v___y_718_ = v_a_732_;
v___y_719_ = v___x_781_;
v___y_720_ = v___x_789_;
goto v___jp_717_;
}
}
else
{
lean_object* v_a_827_; 
lean_dec(v_name_602_);
v_a_827_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_786_);
v___y_713_ = v_a_732_;
v___y_714_ = v___x_781_;
v_a_715_ = v_a_827_;
goto v___jp_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_mkCasesOn(v_declName_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object* v_00_u03b1_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_00_u03b1_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(v_00_u03b1_899_, v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_declName_907_, uint8_t v_s_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_907_, v_s_908_, v___y_910_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_declName_915_, lean_object* v_s_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v_s_boxed_922_; lean_object* v_res_923_; 
v_s_boxed_922_ = lean_unbox(v_s_916_);
v_res_923_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(v_declName_915_, v_s_boxed_922_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9(lean_object* v_00_u03b1_924_, lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___redArg(v_x_925_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9___boxed(lean_object* v_00_u03b1_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__5_spec__9(v_00_u03b1_932_, v_x_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___redArg();
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__5(v_00_u03b1_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_954_, lean_object* v_ex_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_962_, lean_object* v_ex_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(v_00_u03b1_962_, v_ex_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(v_00_u03b1_978_, v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_1047_ = 0;
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_1049_ = l_Lean_registerTraceClass(v___x_1046_, v___x_1047_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_1051_;
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

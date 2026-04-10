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
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_mkCasesOn___closed__0 = (const lean_object*)&l_Lean_mkCasesOn___closed__0_value;
static const lean_string_object l_Lean_mkCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCasesOn"};
static const lean_object* l_Lean_mkCasesOn___closed__1 = (const lean_object*)&l_Lean_mkCasesOn___closed__1_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkCasesOn___closed__2_value_aux_0),((lean_object*)&l_Lean_mkCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 62, 169, 32, 175, 179, 252, 201)}};
static const lean_object* l_Lean_mkCasesOn___closed__2 = (const lean_object*)&l_Lean_mkCasesOn___closed__2_value;
static const lean_string_object l_Lean_mkCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkCasesOn___closed__3 = (const lean_object*)&l_Lean_mkCasesOn___closed__3_value;
static const lean_string_object l_Lean_mkCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_mkCasesOn___closed__4 = (const lean_object*)&l_Lean_mkCasesOn___closed__4_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_mkCasesOn___closed__5 = (const lean_object*)&l_Lean_mkCasesOn___closed__5_value;
static lean_once_cell_t l_Lean_mkCasesOn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOn___closed__6;
static lean_once_cell_t l_Lean_mkCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(32u);
v___x_7_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = ((size_t)5ULL);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_unsigned_to_nat(32u);
v___x_12_ = lean_mk_empty_array_with_capacity(v___x_11_);
v___x_13_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0);
v___x_14_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_10_);
lean_ctor_set(v___x_14_, 3, v___x_10_);
lean_ctor_set_usize(v___x_14_, 4, v___x_9_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_traceState_18_; lean_object* v_traces_19_; lean_object* v___x_20_; lean_object* v_traceState_21_; lean_object* v_env_22_; lean_object* v_nextMacroScope_23_; lean_object* v_ngen_24_; lean_object* v_auxDeclNGen_25_; lean_object* v_cache_26_; lean_object* v_messages_27_; lean_object* v_infoState_28_; lean_object* v_snapshotTasks_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_48_; 
v___x_17_ = lean_st_ref_get(v___y_15_);
v_traceState_18_ = lean_ctor_get(v___x_17_, 4);
lean_inc_ref(v_traceState_18_);
lean_dec(v___x_17_);
v_traces_19_ = lean_ctor_get(v_traceState_18_, 0);
lean_inc_ref(v_traces_19_);
lean_dec_ref(v_traceState_18_);
v___x_20_ = lean_st_ref_take(v___y_15_);
v_traceState_21_ = lean_ctor_get(v___x_20_, 4);
v_env_22_ = lean_ctor_get(v___x_20_, 0);
v_nextMacroScope_23_ = lean_ctor_get(v___x_20_, 1);
v_ngen_24_ = lean_ctor_get(v___x_20_, 2);
v_auxDeclNGen_25_ = lean_ctor_get(v___x_20_, 3);
v_cache_26_ = lean_ctor_get(v___x_20_, 5);
v_messages_27_ = lean_ctor_get(v___x_20_, 6);
v_infoState_28_ = lean_ctor_get(v___x_20_, 7);
v_snapshotTasks_29_ = lean_ctor_get(v___x_20_, 8);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_48_ == 0)
{
v___x_31_ = v___x_20_;
v_isShared_32_ = v_isSharedCheck_48_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_snapshotTasks_29_);
lean_inc(v_infoState_28_);
lean_inc(v_messages_27_);
lean_inc(v_cache_26_);
lean_inc(v_traceState_21_);
lean_inc(v_auxDeclNGen_25_);
lean_inc(v_ngen_24_);
lean_inc(v_nextMacroScope_23_);
lean_inc(v_env_22_);
lean_dec(v___x_20_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_48_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint64_t v_tid_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_46_; 
v_tid_33_ = lean_ctor_get_uint64(v_traceState_21_, sizeof(void*)*1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_traceState_21_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; 
v_unused_47_ = lean_ctor_get(v_traceState_21_, 0);
lean_dec(v_unused_47_);
v___x_35_ = v_traceState_21_;
v_isShared_36_ = v_isSharedCheck_46_;
goto v_resetjp_34_;
}
else
{
lean_dec(v_traceState_21_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_46_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_37_);
lean_ctor_set_uint64(v_reuseFailAlloc_45_, sizeof(void*)*1, v_tid_33_);
v___x_39_ = v_reuseFailAlloc_45_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_41_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v___x_39_);
v___x_41_ = v___x_31_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_env_22_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_nextMacroScope_23_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_ngen_24_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_auxDeclNGen_25_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_44_, 5, v_cache_26_);
lean_ctor_set(v_reuseFailAlloc_44_, 6, v_messages_27_);
lean_ctor_set(v_reuseFailAlloc_44_, 7, v_infoState_28_);
lean_ctor_set(v_reuseFailAlloc_44_, 8, v_snapshotTasks_29_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_st_ref_set(v___y_15_, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_traces_19_);
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_49_);
lean_dec(v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___boxed(lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(lean_object* v_opts_64_, lean_object* v_opt_65_){
_start:
{
lean_object* v_name_66_; lean_object* v_defValue_67_; lean_object* v_map_68_; lean_object* v___x_69_; 
v_name_66_ = lean_ctor_get(v_opt_65_, 0);
v_defValue_67_ = lean_ctor_get(v_opt_65_, 1);
v_map_68_ = lean_ctor_get(v_opts_64_, 0);
v___x_69_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_68_, v_name_66_);
if (lean_obj_tag(v___x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = lean_unbox(v_defValue_67_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; 
v_val_71_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v___x_69_);
if (lean_obj_tag(v_val_71_) == 1)
{
uint8_t v_v_72_; 
v_v_72_ = lean_ctor_get_uint8(v_val_71_, 0);
lean_dec_ref(v_val_71_);
return v_v_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec(v_val_71_);
v___x_73_ = lean_unbox(v_defValue_67_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3___boxed(lean_object* v_opts_74_, lean_object* v_opt_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_74_, v_opt_75_);
lean_dec_ref(v_opt_75_);
lean_dec_ref(v_opts_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object* v_declName_78_, lean_object* v_x_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = l_Lean_MessageData_ofName(v_declName_78_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object* v_declName_87_, lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_mkCasesOn___lam__0(v_declName_87_, v_x_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec_ref(v_x_88_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v_env_102_; lean_object* v___x_103_; lean_object* v_mctx_104_; lean_object* v_lctx_105_; lean_object* v_options_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_101_ = lean_st_ref_get(v___y_99_);
v_env_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_env_102_);
lean_dec(v___x_101_);
v___x_103_ = lean_st_ref_get(v___y_97_);
v_mctx_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_mctx_104_);
lean_dec(v___x_103_);
v_lctx_105_ = lean_ctor_get(v___y_96_, 2);
v_options_106_ = lean_ctor_get(v___y_98_, 2);
lean_inc_ref(v_options_106_);
lean_inc_ref(v_lctx_105_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v_env_102_);
lean_ctor_set(v___x_107_, 1, v_mctx_104_);
lean_ctor_set(v___x_107_, 2, v_lctx_105_);
lean_ctor_set(v___x_107_, 3, v_options_106_);
v___x_108_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_msgData_95_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msgData_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_ref_123_; lean_object* v___x_124_; lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_133_; 
v_ref_123_ = lean_ctor_get(v___y_120_, 5);
v___x_124_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_133_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_inc(v_ref_123_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ref_123_);
lean_ctor_set(v___x_129_, 1, v_a_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 1);
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_interruptExceptionId;
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object* v_ex_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; 
if (lean_obj_tag(v_ex_149_) == 16)
{
lean_object* v___x_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v___x_163_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
v___y_156_ = v___y_150_;
v___y_157_ = v___y_151_;
v___y_158_ = v___y_152_;
v___y_159_ = v___y_153_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v_options_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_options_160_ = lean_ctor_get(v___y_158_, 2);
lean_inc_ref(v_options_160_);
v___x_161_ = l_Lean_Kernel_Exception_toMessageData(v_ex_149_, v_options_160_);
v___x_162_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v___x_161_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_ex_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_185_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_a_185_);
lean_dec_ref(v_x_179_);
v___x_186_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_a_185_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
return v___x_186_;
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v_x_179_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v_x_179_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v_x_179_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 0);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(size_t v_sz_202_, size_t v_i_203_, lean_object* v_bs_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_usize_dec_lt(v_i_203_, v_sz_202_);
if (v___x_205_ == 0)
{
return v_bs_204_;
}
else
{
lean_object* v_v_206_; lean_object* v_msg_207_; lean_object* v___x_208_; lean_object* v_bs_x27_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v_v_206_ = lean_array_uget_borrowed(v_bs_204_, v_i_203_);
v_msg_207_ = lean_ctor_get(v_v_206_, 1);
lean_inc_ref(v_msg_207_);
v___x_208_ = lean_unsigned_to_nat(0u);
v_bs_x27_209_ = lean_array_uset(v_bs_204_, v_i_203_, v___x_208_);
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_add(v_i_203_, v___x_210_);
v___x_212_ = lean_array_uset(v_bs_x27_209_, v_i_203_, v_msg_207_);
v_i_203_ = v___x_211_;
v_bs_204_ = v___x_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10___boxed(lean_object* v_sz_214_, lean_object* v_i_215_, lean_object* v_bs_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_214_);
lean_dec(v_sz_214_);
v_i_boxed_218_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(v_sz_boxed_217_, v_i_boxed_218_, v_bs_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object* v_oldTraces_220_, lean_object* v_data_221_, lean_object* v_ref_222_, lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_fileName_229_; lean_object* v_fileMap_230_; lean_object* v_options_231_; lean_object* v_currRecDepth_232_; lean_object* v_maxRecDepth_233_; lean_object* v_ref_234_; lean_object* v_currNamespace_235_; lean_object* v_openDecls_236_; lean_object* v_initHeartbeats_237_; lean_object* v_maxHeartbeats_238_; lean_object* v_quotContext_239_; lean_object* v_currMacroScope_240_; uint8_t v_diag_241_; lean_object* v_cancelTk_x3f_242_; uint8_t v_suppressElabErrors_243_; lean_object* v_inheritedTraceOptions_244_; lean_object* v___x_245_; lean_object* v_traceState_246_; lean_object* v_traces_247_; lean_object* v_ref_248_; lean_object* v___x_249_; lean_object* v___x_250_; size_t v_sz_251_; size_t v___x_252_; lean_object* v___x_253_; lean_object* v_msg_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_293_; 
v_fileName_229_ = lean_ctor_get(v___y_226_, 0);
v_fileMap_230_ = lean_ctor_get(v___y_226_, 1);
v_options_231_ = lean_ctor_get(v___y_226_, 2);
v_currRecDepth_232_ = lean_ctor_get(v___y_226_, 3);
v_maxRecDepth_233_ = lean_ctor_get(v___y_226_, 4);
v_ref_234_ = lean_ctor_get(v___y_226_, 5);
v_currNamespace_235_ = lean_ctor_get(v___y_226_, 6);
v_openDecls_236_ = lean_ctor_get(v___y_226_, 7);
v_initHeartbeats_237_ = lean_ctor_get(v___y_226_, 8);
v_maxHeartbeats_238_ = lean_ctor_get(v___y_226_, 9);
v_quotContext_239_ = lean_ctor_get(v___y_226_, 10);
v_currMacroScope_240_ = lean_ctor_get(v___y_226_, 11);
v_diag_241_ = lean_ctor_get_uint8(v___y_226_, sizeof(void*)*14);
v_cancelTk_x3f_242_ = lean_ctor_get(v___y_226_, 12);
v_suppressElabErrors_243_ = lean_ctor_get_uint8(v___y_226_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_244_ = lean_ctor_get(v___y_226_, 13);
v___x_245_ = lean_st_ref_get(v___y_227_);
v_traceState_246_ = lean_ctor_get(v___x_245_, 4);
lean_inc_ref(v_traceState_246_);
lean_dec(v___x_245_);
v_traces_247_ = lean_ctor_get(v_traceState_246_, 0);
lean_inc_ref(v_traces_247_);
lean_dec_ref(v_traceState_246_);
v_ref_248_ = l_Lean_replaceRef(v_ref_222_, v_ref_234_);
lean_inc_ref(v_inheritedTraceOptions_244_);
lean_inc(v_cancelTk_x3f_242_);
lean_inc(v_currMacroScope_240_);
lean_inc(v_quotContext_239_);
lean_inc(v_maxHeartbeats_238_);
lean_inc(v_initHeartbeats_237_);
lean_inc(v_openDecls_236_);
lean_inc(v_currNamespace_235_);
lean_inc(v_maxRecDepth_233_);
lean_inc(v_currRecDepth_232_);
lean_inc_ref(v_options_231_);
lean_inc_ref(v_fileMap_230_);
lean_inc_ref(v_fileName_229_);
v___x_249_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_249_, 0, v_fileName_229_);
lean_ctor_set(v___x_249_, 1, v_fileMap_230_);
lean_ctor_set(v___x_249_, 2, v_options_231_);
lean_ctor_set(v___x_249_, 3, v_currRecDepth_232_);
lean_ctor_set(v___x_249_, 4, v_maxRecDepth_233_);
lean_ctor_set(v___x_249_, 5, v_ref_248_);
lean_ctor_set(v___x_249_, 6, v_currNamespace_235_);
lean_ctor_set(v___x_249_, 7, v_openDecls_236_);
lean_ctor_set(v___x_249_, 8, v_initHeartbeats_237_);
lean_ctor_set(v___x_249_, 9, v_maxHeartbeats_238_);
lean_ctor_set(v___x_249_, 10, v_quotContext_239_);
lean_ctor_set(v___x_249_, 11, v_currMacroScope_240_);
lean_ctor_set(v___x_249_, 12, v_cancelTk_x3f_242_);
lean_ctor_set(v___x_249_, 13, v_inheritedTraceOptions_244_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*14, v_diag_241_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*14 + 1, v_suppressElabErrors_243_);
v___x_250_ = l_Lean_PersistentArray_toArray___redArg(v_traces_247_);
lean_dec_ref(v_traces_247_);
v_sz_251_ = lean_array_size(v___x_250_);
v___x_252_ = ((size_t)0ULL);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(v_sz_251_, v___x_252_, v___x_250_);
v_msg_254_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_254_, 0, v_data_221_);
lean_ctor_set(v_msg_254_, 1, v_msg_223_);
lean_ctor_set(v_msg_254_, 2, v___x_253_);
v___x_255_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msg_254_, v___y_224_, v___y_225_, v___x_249_, v___y_227_);
lean_dec_ref(v___x_249_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_293_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_293_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_293_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v_traceState_261_; lean_object* v_env_262_; lean_object* v_nextMacroScope_263_; lean_object* v_ngen_264_; lean_object* v_auxDeclNGen_265_; lean_object* v_cache_266_; lean_object* v_messages_267_; lean_object* v_infoState_268_; lean_object* v_snapshotTasks_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_292_; 
v___x_260_ = lean_st_ref_take(v___y_227_);
v_traceState_261_ = lean_ctor_get(v___x_260_, 4);
v_env_262_ = lean_ctor_get(v___x_260_, 0);
v_nextMacroScope_263_ = lean_ctor_get(v___x_260_, 1);
v_ngen_264_ = lean_ctor_get(v___x_260_, 2);
v_auxDeclNGen_265_ = lean_ctor_get(v___x_260_, 3);
v_cache_266_ = lean_ctor_get(v___x_260_, 5);
v_messages_267_ = lean_ctor_get(v___x_260_, 6);
v_infoState_268_ = lean_ctor_get(v___x_260_, 7);
v_snapshotTasks_269_ = lean_ctor_get(v___x_260_, 8);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_292_ == 0)
{
v___x_271_ = v___x_260_;
v_isShared_272_ = v_isSharedCheck_292_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_snapshotTasks_269_);
lean_inc(v_infoState_268_);
lean_inc(v_messages_267_);
lean_inc(v_cache_266_);
lean_inc(v_traceState_261_);
lean_inc(v_auxDeclNGen_265_);
lean_inc(v_ngen_264_);
lean_inc(v_nextMacroScope_263_);
lean_inc(v_env_262_);
lean_dec(v___x_260_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_292_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint64_t v_tid_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_290_; 
v_tid_273_ = lean_ctor_get_uint64(v_traceState_261_, sizeof(void*)*1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_traceState_261_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v_traceState_261_, 0);
lean_dec(v_unused_291_);
v___x_275_ = v_traceState_261_;
v_isShared_276_ = v_isSharedCheck_290_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_traceState_261_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_290_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_ref_222_);
lean_ctor_set(v___x_277_, 1, v_a_256_);
v___x_278_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_220_, v___x_277_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_278_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_278_);
lean_ctor_set_uint64(v_reuseFailAlloc_289_, sizeof(void*)*1, v_tid_273_);
v___x_280_ = v_reuseFailAlloc_289_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v___x_280_);
v___x_282_ = v___x_271_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_env_262_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_nextMacroScope_263_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_ngen_264_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_auxDeclNGen_265_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_288_, 5, v_cache_266_);
lean_ctor_set(v_reuseFailAlloc_288_, 6, v_messages_267_);
lean_ctor_set(v_reuseFailAlloc_288_, 7, v_infoState_268_);
lean_ctor_set(v_reuseFailAlloc_288_, 8, v_snapshotTasks_269_);
v___x_282_ = v_reuseFailAlloc_288_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_st_ref_set(v___y_227_, v___x_282_);
v___x_284_ = lean_box(0);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_284_);
v___x_286_ = v___x_258_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object* v_oldTraces_294_, lean_object* v_data_295_, lean_object* v_ref_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_oldTraces_294_, v_data_295_, v_ref_296_, v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_a_306_ = lean_ctor_get(v_x_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v_x_304_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v_x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v_x_304_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v_x_304_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v_x_304_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 0);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg___boxed(lean_object* v_x_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_x_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object* v_opts_325_, lean_object* v_opt_326_){
_start:
{
lean_object* v_name_327_; lean_object* v_defValue_328_; lean_object* v_map_329_; lean_object* v___x_330_; 
v_name_327_ = lean_ctor_get(v_opt_326_, 0);
v_defValue_328_ = lean_ctor_get(v_opt_326_, 1);
v_map_329_ = lean_ctor_get(v_opts_325_, 0);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_329_, v_name_327_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_inc(v_defValue_328_);
return v_defValue_328_;
}
else
{
lean_object* v_val_331_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v___x_330_);
if (lean_obj_tag(v_val_331_) == 3)
{
lean_object* v_v_332_; 
v_v_332_ = lean_ctor_get(v_val_331_, 0);
lean_inc(v_v_332_);
lean_dec_ref(v_val_331_);
return v_v_332_;
}
else
{
lean_dec(v_val_331_);
lean_inc(v_defValue_328_);
return v_defValue_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object* v_opts_333_, lean_object* v_opt_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_333_, v_opt_334_);
lean_dec_ref(v_opt_334_);
lean_dec_ref(v_opts_333_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object* v_e_336_){
_start:
{
if (lean_obj_tag(v_e_336_) == 0)
{
uint8_t v___x_337_; 
v___x_337_ = 2;
return v___x_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object* v_e_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_e_339_);
lean_dec_ref(v_e_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2(void){
_start:
{
lean_object* v___x_345_; double v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_float_of_nat(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5(void){
_start:
{
lean_object* v___x_350_; double v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1000u);
v___x_351_ = lean_float_of_nat(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object* v_cls_352_, uint8_t v_collapsed_353_, lean_object* v_tag_354_, lean_object* v_opts_355_, uint8_t v_clsEnabled_356_, lean_object* v_oldTraces_357_, lean_object* v_msg_358_, lean_object* v_resStartStop_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_456_; 
v_fst_365_ = lean_ctor_get(v_resStartStop_359_, 0);
v_snd_366_ = lean_ctor_get(v_resStartStop_359_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_resStartStop_359_);
if (v_isSharedCheck_456_ == 0)
{
v___x_368_ = v_resStartStop_359_;
v_isShared_369_ = v_isSharedCheck_456_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_365_);
lean_dec(v_resStartStop_359_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_456_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v_data_373_; lean_object* v_fst_376_; lean_object* v_snd_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_455_; 
v_fst_376_ = lean_ctor_get(v_snd_366_, 0);
v_snd_377_ = lean_ctor_get(v_snd_366_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_snd_366_);
if (v_isSharedCheck_455_ == 0)
{
v___x_379_ = v_snd_366_;
v_isShared_380_ = v_isSharedCheck_455_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snd_377_);
lean_inc(v_fst_376_);
lean_dec(v_snd_366_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_455_;
goto v_resetjp_378_;
}
v___jp_370_:
{
lean_object* v___x_374_; 
lean_inc(v___y_372_);
v___x_374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_oldTraces_357_, v_data_373_, v___y_372_, v___y_371_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_375_; 
lean_dec_ref(v___x_374_);
v___x_375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_fst_365_);
return v___x_375_;
}
else
{
lean_dec(v_fst_365_);
return v___x_374_;
}
}
v_resetjp_378_:
{
lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___y_384_; lean_object* v_a_385_; uint8_t v___y_409_; double v___y_440_; 
v___x_381_ = l_Lean_trace_profiler;
v___x_382_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_355_, v___x_381_);
if (v___x_382_ == 0)
{
v___y_409_ = v___x_382_;
goto v___jp_408_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = l_Lean_trace_profiler_useHeartbeats;
v___x_446_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_355_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; double v___x_449_; double v___x_450_; double v___x_451_; 
v___x_447_ = l_Lean_trace_profiler_threshold;
v___x_448_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_355_, v___x_447_);
v___x_449_ = lean_float_of_nat(v___x_448_);
v___x_450_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5);
v___x_451_ = lean_float_div(v___x_449_, v___x_450_);
v___y_440_ = v___x_451_;
goto v___jp_439_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; double v___x_454_; 
v___x_452_ = l_Lean_trace_profiler_threshold;
v___x_453_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_355_, v___x_452_);
v___x_454_ = lean_float_of_nat(v___x_453_);
v___y_440_ = v___x_454_;
goto v___jp_439_;
}
}
v___jp_383_:
{
uint8_t v_result_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v_result_386_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_fst_365_);
v___x_387_ = l_Lean_TraceResult_toEmoji(v_result_386_);
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
v___x_389_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 7);
lean_ctor_set(v___x_379_, 1, v___x_389_);
lean_ctor_set(v___x_379_, 0, v___x_388_);
v___x_391_ = v___x_379_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_402_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v_m_393_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 7);
lean_ctor_set(v___x_368_, 1, v_a_385_);
lean_ctor_set(v___x_368_, 0, v___x_391_);
v_m_393_ = v___x_368_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_a_385_);
v_m_393_ = v_reuseFailAlloc_401_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; double v___x_396_; lean_object* v_data_397_; 
v___x_394_ = lean_box(v_result_386_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v___x_396_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2);
lean_inc_ref(v_tag_354_);
lean_inc_ref(v___x_395_);
lean_inc(v_cls_352_);
v_data_397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_397_, 0, v_cls_352_);
lean_ctor_set(v_data_397_, 1, v___x_395_);
lean_ctor_set(v_data_397_, 2, v_tag_354_);
lean_ctor_set_float(v_data_397_, sizeof(void*)*3, v___x_396_);
lean_ctor_set_float(v_data_397_, sizeof(void*)*3 + 8, v___x_396_);
lean_ctor_set_uint8(v_data_397_, sizeof(void*)*3 + 16, v_collapsed_353_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_395_);
lean_dec(v_snd_377_);
lean_dec(v_fst_376_);
lean_dec_ref(v_tag_354_);
lean_dec(v_cls_352_);
v___y_371_ = v_m_393_;
v___y_372_ = v___y_384_;
v_data_373_ = v_data_397_;
goto v___jp_370_;
}
else
{
lean_object* v_data_398_; double v___x_399_; double v___x_400_; 
lean_dec_ref(v_data_397_);
v_data_398_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_398_, 0, v_cls_352_);
lean_ctor_set(v_data_398_, 1, v___x_395_);
lean_ctor_set(v_data_398_, 2, v_tag_354_);
v___x_399_ = lean_unbox_float(v_fst_376_);
lean_dec(v_fst_376_);
lean_ctor_set_float(v_data_398_, sizeof(void*)*3, v___x_399_);
v___x_400_ = lean_unbox_float(v_snd_377_);
lean_dec(v_snd_377_);
lean_ctor_set_float(v_data_398_, sizeof(void*)*3 + 8, v___x_400_);
lean_ctor_set_uint8(v_data_398_, sizeof(void*)*3 + 16, v_collapsed_353_);
v___y_371_ = v_m_393_;
v___y_372_ = v___y_384_;
v_data_373_ = v_data_398_;
goto v___jp_370_;
}
}
}
}
v___jp_403_:
{
lean_object* v_ref_404_; lean_object* v___x_405_; 
v_ref_404_ = lean_ctor_get(v___y_362_, 5);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
lean_inc(v_fst_365_);
v___x_405_ = lean_apply_6(v_msg_358_, v_fst_365_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, lean_box(0));
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___y_384_ = v_ref_404_;
v_a_385_ = v_a_406_;
goto v___jp_383_;
}
else
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_405_);
v___x_407_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4);
v___y_384_ = v_ref_404_;
v_a_385_ = v___x_407_;
goto v___jp_383_;
}
}
v___jp_408_:
{
if (v_clsEnabled_356_ == 0)
{
if (v___y_409_ == 0)
{
lean_object* v___x_410_; lean_object* v_traceState_411_; lean_object* v_env_412_; lean_object* v_nextMacroScope_413_; lean_object* v_ngen_414_; lean_object* v_auxDeclNGen_415_; lean_object* v_cache_416_; lean_object* v_messages_417_; lean_object* v_infoState_418_; lean_object* v_snapshotTasks_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_379_);
lean_dec(v_snd_377_);
lean_dec(v_fst_376_);
lean_del_object(v___x_368_);
lean_dec_ref(v_msg_358_);
lean_dec_ref(v_tag_354_);
lean_dec(v_cls_352_);
v___x_410_ = lean_st_ref_take(v___y_363_);
v_traceState_411_ = lean_ctor_get(v___x_410_, 4);
v_env_412_ = lean_ctor_get(v___x_410_, 0);
v_nextMacroScope_413_ = lean_ctor_get(v___x_410_, 1);
v_ngen_414_ = lean_ctor_get(v___x_410_, 2);
v_auxDeclNGen_415_ = lean_ctor_get(v___x_410_, 3);
v_cache_416_ = lean_ctor_get(v___x_410_, 5);
v_messages_417_ = lean_ctor_get(v___x_410_, 6);
v_infoState_418_ = lean_ctor_get(v___x_410_, 7);
v_snapshotTasks_419_ = lean_ctor_get(v___x_410_, 8);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_438_ == 0)
{
v___x_421_ = v___x_410_;
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snapshotTasks_419_);
lean_inc(v_infoState_418_);
lean_inc(v_messages_417_);
lean_inc(v_cache_416_);
lean_inc(v_traceState_411_);
lean_inc(v_auxDeclNGen_415_);
lean_inc(v_ngen_414_);
lean_inc(v_nextMacroScope_413_);
lean_inc(v_env_412_);
lean_dec(v___x_410_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint64_t v_tid_423_; lean_object* v_traces_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_437_; 
v_tid_423_ = lean_ctor_get_uint64(v_traceState_411_, sizeof(void*)*1);
v_traces_424_ = lean_ctor_get(v_traceState_411_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_traceState_411_);
if (v_isSharedCheck_437_ == 0)
{
v___x_426_ = v_traceState_411_;
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_traces_424_);
lean_dec(v_traceState_411_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_357_, v_traces_424_);
lean_dec_ref(v_traces_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_428_);
lean_ctor_set_uint64(v_reuseFailAlloc_436_, sizeof(void*)*1, v_tid_423_);
v___x_430_ = v_reuseFailAlloc_436_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 4, v___x_430_);
v___x_432_ = v___x_421_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_env_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_nextMacroScope_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_ngen_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_auxDeclNGen_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_cache_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_messages_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_infoState_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_snapshotTasks_419_);
v___x_432_ = v_reuseFailAlloc_435_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_st_ref_set(v___y_363_, v___x_432_);
v___x_434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_fst_365_);
return v___x_434_;
}
}
}
}
}
else
{
goto v___jp_403_;
}
}
else
{
goto v___jp_403_;
}
}
v___jp_439_:
{
double v___x_441_; double v___x_442_; double v___x_443_; uint8_t v___x_444_; 
v___x_441_ = lean_unbox_float(v_snd_377_);
v___x_442_ = lean_unbox_float(v_fst_376_);
v___x_443_ = lean_float_sub(v___x_441_, v___x_442_);
v___x_444_ = lean_float_decLt(v___y_440_, v___x_443_);
v___y_409_ = v___x_444_;
goto v___jp_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_cls_457_, lean_object* v_collapsed_458_, lean_object* v_tag_459_, lean_object* v_opts_460_, lean_object* v_clsEnabled_461_, lean_object* v_oldTraces_462_, lean_object* v_msg_463_, lean_object* v_resStartStop_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v_collapsed_boxed_470_; uint8_t v_clsEnabled_boxed_471_; lean_object* v_res_472_; 
v_collapsed_boxed_470_ = lean_unbox(v_collapsed_458_);
v_clsEnabled_boxed_471_ = lean_unbox(v_clsEnabled_461_);
v_res_472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v_cls_457_, v_collapsed_boxed_470_, v_tag_459_, v_opts_460_, v_clsEnabled_boxed_471_, v_oldTraces_462_, v_msg_463_, v_resStartStop_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec_ref(v_opts_460_);
return v_res_472_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_473_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set(v___x_479_, 3, v___x_478_);
lean_ctor_set(v___x_479_, 4, v___x_478_);
lean_ctor_set(v___x_479_, 5, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object* v_declName_480_, uint8_t v_s_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v_nextMacroScope_487_; lean_object* v_ngen_488_; lean_object* v_auxDeclNGen_489_; lean_object* v_traceState_490_; lean_object* v_messages_491_; lean_object* v_infoState_492_; lean_object* v_snapshotTasks_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_522_; 
v___x_485_ = lean_st_ref_take(v___y_483_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
v_nextMacroScope_487_ = lean_ctor_get(v___x_485_, 1);
v_ngen_488_ = lean_ctor_get(v___x_485_, 2);
v_auxDeclNGen_489_ = lean_ctor_get(v___x_485_, 3);
v_traceState_490_ = lean_ctor_get(v___x_485_, 4);
v_messages_491_ = lean_ctor_get(v___x_485_, 6);
v_infoState_492_ = lean_ctor_get(v___x_485_, 7);
v_snapshotTasks_493_ = lean_ctor_get(v___x_485_, 8);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_485_, 5);
lean_dec(v_unused_523_);
v___x_495_ = v___x_485_;
v_isShared_496_ = v_isSharedCheck_522_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_snapshotTasks_493_);
lean_inc(v_infoState_492_);
lean_inc(v_messages_491_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_489_);
lean_inc(v_ngen_488_);
lean_inc(v_nextMacroScope_487_);
lean_inc(v_env_486_);
lean_dec(v___x_485_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_522_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_497_ = 0;
v___x_498_ = lean_box(0);
v___x_499_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_486_, v_declName_480_, v_s_481_, v___x_497_, v___x_498_);
v___x_500_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 5, v___x_500_);
lean_ctor_set(v___x_495_, 0, v___x_499_);
v___x_502_ = v___x_495_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_nextMacroScope_487_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_ngen_488_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_auxDeclNGen_489_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_traceState_490_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_messages_491_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v_infoState_492_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_snapshotTasks_493_);
v___x_502_ = v_reuseFailAlloc_521_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_mctx_505_; lean_object* v_zetaDeltaFVarIds_506_; lean_object* v_postponed_507_; lean_object* v_diag_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_519_; 
v___x_503_ = lean_st_ref_set(v___y_483_, v___x_502_);
v___x_504_ = lean_st_ref_take(v___y_482_);
v_mctx_505_ = lean_ctor_get(v___x_504_, 0);
v_zetaDeltaFVarIds_506_ = lean_ctor_get(v___x_504_, 2);
v_postponed_507_ = lean_ctor_get(v___x_504_, 3);
v_diag_508_ = lean_ctor_get(v___x_504_, 4);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_504_, 1);
lean_dec(v_unused_520_);
v___x_510_ = v___x_504_;
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_diag_508_);
lean_inc(v_postponed_507_);
lean_inc(v_zetaDeltaFVarIds_506_);
lean_inc(v_mctx_505_);
lean_dec(v___x_504_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_mctx_505_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_zetaDeltaFVarIds_506_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_postponed_507_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_diag_508_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_st_ref_set(v___y_482_, v___x_514_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_declName_524_, lean_object* v_s_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_s_boxed_529_; lean_object* v_res_530_; 
v_s_boxed_529_ = lean_unbox(v_s_525_);
v_res_530_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_524_, v_s_boxed_529_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec(v___y_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(lean_object* v_declName_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v___x_537_; lean_object* v___x_538_; 
v___x_537_ = 0;
v___x_538_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_531_, v___x_537_, v___y_533_, v___y_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_declName_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_declName_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
static lean_object* _init_l_Lean_mkCasesOn___closed__6(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_556_ = ((lean_object*)(l_Lean_mkCasesOn___closed__5));
v___x_557_ = l_Lean_Name_append(v___x_556_, v___x_555_);
return v___x_557_;
}
}
static double _init_l_Lean_mkCasesOn___closed__7(void){
_start:
{
lean_object* v___x_558_; double v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1000000000u);
v___x_559_ = lean_float_of_nat(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_options_566_; lean_object* v_inheritedTraceOptions_567_; uint8_t v_hasTrace_568_; lean_object* v_name_569_; 
v_options_566_ = lean_ctor_get(v_a_563_, 2);
v_inheritedTraceOptions_567_ = lean_ctor_get(v_a_563_, 13);
v_hasTrace_568_ = lean_ctor_get_uint8(v_options_566_, sizeof(void*)*1);
lean_inc(v_declName_560_);
v_name_569_ = l_Lean_mkCasesOnName(v_declName_560_);
if (v_hasTrace_568_ == 0)
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = lean_st_ref_get(v_a_564_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_elab_environment_to_kernel_env(v_env_571_);
v___x_573_ = lean_mk_cases_on(v___x_572_, v_declName_560_);
lean_dec(v_declName_560_);
v___x_574_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_573_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_addDecl(v_a_575_, v_hasTrace_568_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_env_579_; lean_object* v_nextMacroScope_580_; lean_object* v_ngen_581_; lean_object* v_auxDeclNGen_582_; lean_object* v_traceState_583_; lean_object* v_messages_584_; lean_object* v_infoState_585_; lean_object* v_snapshotTasks_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v___x_576_);
lean_inc(v_name_569_);
v___x_577_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_569_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec_ref(v___x_577_);
v___x_578_ = lean_st_ref_take(v_a_564_);
v_env_579_ = lean_ctor_get(v___x_578_, 0);
v_nextMacroScope_580_ = lean_ctor_get(v___x_578_, 1);
v_ngen_581_ = lean_ctor_get(v___x_578_, 2);
v_auxDeclNGen_582_ = lean_ctor_get(v___x_578_, 3);
v_traceState_583_ = lean_ctor_get(v___x_578_, 4);
v_messages_584_ = lean_ctor_get(v___x_578_, 6);
v_infoState_585_ = lean_ctor_get(v___x_578_, 7);
v_snapshotTasks_586_ = lean_ctor_get(v___x_578_, 8);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_578_, 5);
lean_dec(v_unused_613_);
v___x_588_ = v___x_578_;
v_isShared_589_ = v_isSharedCheck_612_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snapshotTasks_586_);
lean_inc(v_infoState_585_);
lean_inc(v_messages_584_);
lean_inc(v_traceState_583_);
lean_inc(v_auxDeclNGen_582_);
lean_inc(v_ngen_581_);
lean_inc(v_nextMacroScope_580_);
lean_inc(v_env_579_);
lean_dec(v___x_578_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_612_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
lean_inc(v_name_569_);
v___x_590_ = l_Lean_markAuxRecursor(v_env_579_, v_name_569_);
v___x_591_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 5, v___x_591_);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_nextMacroScope_580_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_ngen_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_auxDeclNGen_582_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_traceState_583_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_messages_584_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_infoState_585_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_snapshotTasks_586_);
v___x_593_ = v_reuseFailAlloc_611_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_mctx_596_; lean_object* v_zetaDeltaFVarIds_597_; lean_object* v_postponed_598_; lean_object* v_diag_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_609_; 
v___x_594_ = lean_st_ref_set(v_a_564_, v___x_593_);
v___x_595_ = lean_st_ref_take(v_a_562_);
v_mctx_596_ = lean_ctor_get(v___x_595_, 0);
v_zetaDeltaFVarIds_597_ = lean_ctor_get(v___x_595_, 2);
v_postponed_598_ = lean_ctor_get(v___x_595_, 3);
v_diag_599_ = lean_ctor_get(v___x_595_, 4);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_595_, 1);
lean_dec(v_unused_610_);
v___x_601_ = v___x_595_;
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_diag_599_);
lean_inc(v_postponed_598_);
lean_inc(v_zetaDeltaFVarIds_597_);
lean_inc(v_mctx_596_);
lean_dec(v___x_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_mctx_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_zetaDeltaFVarIds_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_postponed_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_diag_599_);
v___x_605_ = v_reuseFailAlloc_608_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_st_ref_set(v_a_562_, v___x_605_);
v___x_607_ = l_Lean_enableRealizationsForConst(v_name_569_, v_a_563_, v_a_564_);
return v___x_607_;
}
}
}
}
}
else
{
lean_dec(v_name_569_);
return v___x_576_;
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_name_569_);
v_a_614_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_574_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_574_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_a_630_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v_a_645_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v_a_663_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v_a_675_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; 
lean_inc(v_declName_560_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_622_, 0, v_declName_560_);
v___x_623_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_624_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_625_ = lean_obj_once(&l_Lean_mkCasesOn___closed__6, &l_Lean_mkCasesOn___closed__6_once, _init_l_Lean_mkCasesOn___closed__6);
v___x_626_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_567_, v_options_566_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = l_Lean_trace_profiler;
v___x_789_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_566_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v_env_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec_ref(v___f_622_);
v___x_790_ = lean_st_ref_get(v_a_564_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_env_791_);
lean_dec(v___x_790_);
v___x_792_ = lean_elab_environment_to_kernel_env(v_env_791_);
v___x_793_ = lean_mk_cases_on(v___x_792_, v_declName_560_);
lean_dec(v_declName_560_);
v___x_794_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_793_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_addDecl(v_a_795_, v___x_789_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_env_799_; lean_object* v_nextMacroScope_800_; lean_object* v_ngen_801_; lean_object* v_auxDeclNGen_802_; lean_object* v_traceState_803_; lean_object* v_messages_804_; lean_object* v_infoState_805_; lean_object* v_snapshotTasks_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___x_796_);
lean_inc(v_name_569_);
v___x_797_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_569_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec_ref(v___x_797_);
v___x_798_ = lean_st_ref_take(v_a_564_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
v_nextMacroScope_800_ = lean_ctor_get(v___x_798_, 1);
v_ngen_801_ = lean_ctor_get(v___x_798_, 2);
v_auxDeclNGen_802_ = lean_ctor_get(v___x_798_, 3);
v_traceState_803_ = lean_ctor_get(v___x_798_, 4);
v_messages_804_ = lean_ctor_get(v___x_798_, 6);
v_infoState_805_ = lean_ctor_get(v___x_798_, 7);
v_snapshotTasks_806_ = lean_ctor_get(v___x_798_, 8);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_798_, 5);
lean_dec(v_unused_833_);
v___x_808_ = v___x_798_;
v_isShared_809_ = v_isSharedCheck_832_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_snapshotTasks_806_);
lean_inc(v_infoState_805_);
lean_inc(v_messages_804_);
lean_inc(v_traceState_803_);
lean_inc(v_auxDeclNGen_802_);
lean_inc(v_ngen_801_);
lean_inc(v_nextMacroScope_800_);
lean_inc(v_env_799_);
lean_dec(v___x_798_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_832_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_name_569_);
v___x_810_ = l_Lean_markAuxRecursor(v_env_799_, v_name_569_);
v___x_811_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 5, v___x_811_);
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_nextMacroScope_800_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_ngen_801_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_auxDeclNGen_802_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_traceState_803_);
lean_ctor_set(v_reuseFailAlloc_831_, 5, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 6, v_messages_804_);
lean_ctor_set(v_reuseFailAlloc_831_, 7, v_infoState_805_);
lean_ctor_set(v_reuseFailAlloc_831_, 8, v_snapshotTasks_806_);
v___x_813_ = v_reuseFailAlloc_831_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_mctx_816_; lean_object* v_zetaDeltaFVarIds_817_; lean_object* v_postponed_818_; lean_object* v_diag_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_829_; 
v___x_814_ = lean_st_ref_set(v_a_564_, v___x_813_);
v___x_815_ = lean_st_ref_take(v_a_562_);
v_mctx_816_ = lean_ctor_get(v___x_815_, 0);
v_zetaDeltaFVarIds_817_ = lean_ctor_get(v___x_815_, 2);
v_postponed_818_ = lean_ctor_get(v___x_815_, 3);
v_diag_819_ = lean_ctor_get(v___x_815_, 4);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_815_, 1);
lean_dec(v_unused_830_);
v___x_821_ = v___x_815_;
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_diag_819_);
lean_inc(v_postponed_818_);
lean_inc(v_zetaDeltaFVarIds_817_);
lean_inc(v_mctx_816_);
lean_dec(v___x_815_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_mctx_816_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_zetaDeltaFVarIds_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_postponed_818_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_diag_819_);
v___x_825_ = v_reuseFailAlloc_828_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_st_ref_set(v_a_562_, v___x_825_);
v___x_827_ = l_Lean_enableRealizationsForConst(v_name_569_, v_a_563_, v_a_564_);
return v___x_827_;
}
}
}
}
}
else
{
lean_dec(v_name_569_);
return v___x_796_;
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_name_569_);
v_a_834_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_794_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_794_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
goto v___jp_690_;
}
}
else
{
goto v___jp_690_;
}
v___jp_627_:
{
lean_object* v___x_631_; double v___x_632_; double v___x_633_; double v___x_634_; double v___x_635_; double v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_631_ = lean_io_mono_nanos_now();
v___x_632_ = lean_float_of_nat(v___y_628_);
v___x_633_ = lean_float_once(&l_Lean_mkCasesOn___closed__7, &l_Lean_mkCasesOn___closed__7_once, _init_l_Lean_mkCasesOn___closed__7);
v___x_634_ = lean_float_div(v___x_632_, v___x_633_);
v___x_635_ = lean_float_of_nat(v___x_631_);
v___x_636_ = lean_float_div(v___x_635_, v___x_633_);
v___x_637_ = lean_box_float(v___x_634_);
v___x_638_ = lean_box_float(v___x_636_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_a_630_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_623_, v_hasTrace_568_, v___x_624_, v_options_566_, v___x_626_, v___y_629_, v___f_622_, v___x_640_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_641_;
}
v___jp_642_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_a_645_);
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v_a_630_ = v___x_646_;
goto v___jp_627_;
}
v___jp_647_:
{
if (lean_obj_tag(v___y_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_a_651_ = lean_ctor_get(v___y_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___y_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___y_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___y_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_628_ = v___y_648_;
v___y_629_ = v___y_649_;
v_a_630_ = v___x_656_;
goto v___jp_627_;
}
}
}
else
{
lean_object* v_a_659_; 
v_a_659_ = lean_ctor_get(v___y_650_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___y_650_);
v___y_643_ = v___y_648_;
v___y_644_ = v___y_649_;
v_a_645_ = v_a_659_;
goto v___jp_642_;
}
}
v___jp_660_:
{
lean_object* v___x_664_; double v___x_665_; double v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_664_ = lean_io_get_num_heartbeats();
v___x_665_ = lean_float_of_nat(v___y_662_);
v___x_666_ = lean_float_of_nat(v___x_664_);
v___x_667_ = lean_box_float(v___x_665_);
v___x_668_ = lean_box_float(v___x_666_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_a_663_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_623_, v_hasTrace_568_, v___x_624_, v_options_566_, v___x_626_, v___y_661_, v___f_622_, v___x_670_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_671_;
}
v___jp_672_:
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_a_675_);
v___y_661_ = v___y_673_;
v___y_662_ = v___y_674_;
v_a_663_ = v___x_676_;
goto v___jp_660_;
}
v___jp_677_:
{
if (lean_obj_tag(v___y_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___y_680_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___y_680_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___y_680_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___y_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 1);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v___y_661_ = v___y_678_;
v___y_662_ = v___y_679_;
v_a_663_ = v___x_686_;
goto v___jp_660_;
}
}
}
else
{
lean_object* v_a_689_; 
v_a_689_ = lean_ctor_get(v___y_680_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___y_680_);
v___y_673_ = v___y_678_;
v___y_674_ = v___y_679_;
v_a_675_ = v_a_689_;
goto v___jp_672_;
}
}
v___jp_690_:
{
lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_691_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v_a_564_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v___x_693_ = l_Lean_trace_profiler_useHeartbeats;
v___x_694_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_566_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_env_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = lean_io_mono_nanos_now();
v___x_696_ = lean_st_ref_get(v_a_564_);
v_env_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc_ref(v_env_697_);
lean_dec(v___x_696_);
v___x_698_ = lean_elab_environment_to_kernel_env(v_env_697_);
v___x_699_ = lean_mk_cases_on(v___x_698_, v_declName_560_);
lean_dec(v_declName_560_);
v___x_700_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_699_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
v___x_702_ = l_Lean_addDecl(v_a_701_, v___x_694_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_env_705_; lean_object* v_nextMacroScope_706_; lean_object* v_ngen_707_; lean_object* v_auxDeclNGen_708_; lean_object* v_traceState_709_; lean_object* v_messages_710_; lean_object* v_infoState_711_; lean_object* v_snapshotTasks_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_702_);
lean_inc(v_name_569_);
v___x_703_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_569_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec_ref(v___x_703_);
v___x_704_ = lean_st_ref_take(v_a_564_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
v_nextMacroScope_706_ = lean_ctor_get(v___x_704_, 1);
v_ngen_707_ = lean_ctor_get(v___x_704_, 2);
v_auxDeclNGen_708_ = lean_ctor_get(v___x_704_, 3);
v_traceState_709_ = lean_ctor_get(v___x_704_, 4);
v_messages_710_ = lean_ctor_get(v___x_704_, 6);
v_infoState_711_ = lean_ctor_get(v___x_704_, 7);
v_snapshotTasks_712_ = lean_ctor_get(v___x_704_, 8);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_704_, 5);
lean_dec(v_unused_739_);
v___x_714_ = v___x_704_;
v_isShared_715_ = v_isSharedCheck_738_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snapshotTasks_712_);
lean_inc(v_infoState_711_);
lean_inc(v_messages_710_);
lean_inc(v_traceState_709_);
lean_inc(v_auxDeclNGen_708_);
lean_inc(v_ngen_707_);
lean_inc(v_nextMacroScope_706_);
lean_inc(v_env_705_);
lean_dec(v___x_704_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_738_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
lean_inc(v_name_569_);
v___x_716_ = l_Lean_markAuxRecursor(v_env_705_, v_name_569_);
v___x_717_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 5, v___x_717_);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_nextMacroScope_706_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_ngen_707_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_auxDeclNGen_708_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_traceState_709_);
lean_ctor_set(v_reuseFailAlloc_737_, 5, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_737_, 6, v_messages_710_);
lean_ctor_set(v_reuseFailAlloc_737_, 7, v_infoState_711_);
lean_ctor_set(v_reuseFailAlloc_737_, 8, v_snapshotTasks_712_);
v___x_719_ = v_reuseFailAlloc_737_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_mctx_722_; lean_object* v_zetaDeltaFVarIds_723_; lean_object* v_postponed_724_; lean_object* v_diag_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
v___x_720_ = lean_st_ref_set(v_a_564_, v___x_719_);
v___x_721_ = lean_st_ref_take(v_a_562_);
v_mctx_722_ = lean_ctor_get(v___x_721_, 0);
v_zetaDeltaFVarIds_723_ = lean_ctor_get(v___x_721_, 2);
v_postponed_724_ = lean_ctor_get(v___x_721_, 3);
v_diag_725_ = lean_ctor_get(v___x_721_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_721_, 1);
lean_dec(v_unused_736_);
v___x_727_ = v___x_721_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_diag_725_);
lean_inc(v_postponed_724_);
lean_inc(v_zetaDeltaFVarIds_723_);
lean_inc(v_mctx_722_);
lean_dec(v___x_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_mctx_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_zetaDeltaFVarIds_723_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_postponed_724_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_diag_725_);
v___x_731_ = v_reuseFailAlloc_734_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_st_ref_set(v_a_562_, v___x_731_);
v___x_733_ = l_Lean_enableRealizationsForConst(v_name_569_, v_a_563_, v_a_564_);
v___y_648_ = v___x_695_;
v___y_649_ = v_a_692_;
v___y_650_ = v___x_733_;
goto v___jp_647_;
}
}
}
}
}
else
{
lean_dec(v_name_569_);
v___y_648_ = v___x_695_;
v___y_649_ = v_a_692_;
v___y_650_ = v___x_702_;
goto v___jp_647_;
}
}
else
{
lean_object* v_a_740_; 
lean_dec(v_name_569_);
v_a_740_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v___x_700_);
v___y_643_ = v___x_695_;
v___y_644_ = v_a_692_;
v_a_645_ = v_a_740_;
goto v___jp_642_;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_env_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_741_ = lean_io_get_num_heartbeats();
v___x_742_ = lean_st_ref_get(v_a_564_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_742_);
v___x_744_ = lean_elab_environment_to_kernel_env(v_env_743_);
v___x_745_ = lean_mk_cases_on(v___x_744_, v_declName_560_);
lean_dec(v_declName_560_);
v___x_746_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_745_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; lean_object* v___x_749_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = 0;
v___x_749_ = l_Lean_addDecl(v_a_747_, v___x_748_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_env_752_; lean_object* v_nextMacroScope_753_; lean_object* v_ngen_754_; lean_object* v_auxDeclNGen_755_; lean_object* v_traceState_756_; lean_object* v_messages_757_; lean_object* v_infoState_758_; lean_object* v_snapshotTasks_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___x_749_);
lean_inc(v_name_569_);
v___x_750_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_569_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec_ref(v___x_750_);
v___x_751_ = lean_st_ref_take(v_a_564_);
v_env_752_ = lean_ctor_get(v___x_751_, 0);
v_nextMacroScope_753_ = lean_ctor_get(v___x_751_, 1);
v_ngen_754_ = lean_ctor_get(v___x_751_, 2);
v_auxDeclNGen_755_ = lean_ctor_get(v___x_751_, 3);
v_traceState_756_ = lean_ctor_get(v___x_751_, 4);
v_messages_757_ = lean_ctor_get(v___x_751_, 6);
v_infoState_758_ = lean_ctor_get(v___x_751_, 7);
v_snapshotTasks_759_ = lean_ctor_get(v___x_751_, 8);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_751_, 5);
lean_dec(v_unused_786_);
v___x_761_ = v___x_751_;
v_isShared_762_ = v_isSharedCheck_785_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snapshotTasks_759_);
lean_inc(v_infoState_758_);
lean_inc(v_messages_757_);
lean_inc(v_traceState_756_);
lean_inc(v_auxDeclNGen_755_);
lean_inc(v_ngen_754_);
lean_inc(v_nextMacroScope_753_);
lean_inc(v_env_752_);
lean_dec(v___x_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_785_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
lean_inc(v_name_569_);
v___x_763_ = l_Lean_markAuxRecursor(v_env_752_, v_name_569_);
v___x_764_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 5, v___x_764_);
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_nextMacroScope_753_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_ngen_754_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_auxDeclNGen_755_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_traceState_756_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_messages_757_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_infoState_758_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_snapshotTasks_759_);
v___x_766_ = v_reuseFailAlloc_784_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_mctx_769_; lean_object* v_zetaDeltaFVarIds_770_; lean_object* v_postponed_771_; lean_object* v_diag_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_782_; 
v___x_767_ = lean_st_ref_set(v_a_564_, v___x_766_);
v___x_768_ = lean_st_ref_take(v_a_562_);
v_mctx_769_ = lean_ctor_get(v___x_768_, 0);
v_zetaDeltaFVarIds_770_ = lean_ctor_get(v___x_768_, 2);
v_postponed_771_ = lean_ctor_get(v___x_768_, 3);
v_diag_772_ = lean_ctor_get(v___x_768_, 4);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_768_, 1);
lean_dec(v_unused_783_);
v___x_774_ = v___x_768_;
v_isShared_775_ = v_isSharedCheck_782_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_diag_772_);
lean_inc(v_postponed_771_);
lean_inc(v_zetaDeltaFVarIds_770_);
lean_inc(v_mctx_769_);
lean_dec(v___x_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_782_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_mctx_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_zetaDeltaFVarIds_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_postponed_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_diag_772_);
v___x_778_ = v_reuseFailAlloc_781_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_st_ref_set(v_a_562_, v___x_778_);
v___x_780_ = l_Lean_enableRealizationsForConst(v_name_569_, v_a_563_, v_a_564_);
v___y_678_ = v_a_692_;
v___y_679_ = v___x_741_;
v___y_680_ = v___x_780_;
goto v___jp_677_;
}
}
}
}
}
else
{
lean_dec(v_name_569_);
v___y_678_ = v_a_692_;
v___y_679_ = v___x_741_;
v___y_680_ = v___x_749_;
goto v___jp_677_;
}
}
else
{
lean_object* v_a_787_; 
lean_dec(v_name_569_);
v_a_787_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_746_);
v___y_673_ = v_a_692_;
v___y_674_ = v___x_741_;
v_a_675_ = v_a_787_;
goto v___jp_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_mkCasesOn(v_declName_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object* v_00_u03b1_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_00_u03b1_857_, lean_object* v_x_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(v_00_u03b1_857_, v_x_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_declName_865_, uint8_t v_s_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_865_, v_s_866_, v___y_868_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_declName_873_, lean_object* v_s_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_s_boxed_880_; lean_object* v_res_881_; 
v_s_boxed_880_ = lean_unbox(v_s_874_);
v_res_881_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(v_declName_873_, v_s_boxed_880_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object* v_00_u03b1_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_x_883_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object* v_00_u03b1_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_00_u03b1_890_, v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(v_00_u03b1_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_912_, lean_object* v_ex_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_920_, lean_object* v_ex_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(v_00_u03b1_920_, v_ex_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_928_, lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v_msg_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_936_, lean_object* v_msg_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(v_00_u03b1_936_, v_msg_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_1005_ = 0;
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_1007_ = l_Lean_registerTraceClass(v___x_1004_, v___x_1005_, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_1009_;
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

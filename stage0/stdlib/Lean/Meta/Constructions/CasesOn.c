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
lean_object* v___x_17_; lean_object* v_traceState_18_; lean_object* v_traces_19_; lean_object* v___x_20_; lean_object* v_traceState_21_; lean_object* v_env_22_; lean_object* v_nextMacroScope_23_; lean_object* v_ngen_24_; lean_object* v_auxDeclNGen_25_; lean_object* v_cache_26_; lean_object* v_messages_27_; lean_object* v_infoState_28_; lean_object* v_snapshotTasks_29_; lean_object* v_newDecls_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_49_; 
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
v_newDecls_30_ = lean_ctor_get(v___x_20_, 9);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_49_ == 0)
{
v___x_32_ = v___x_20_;
v_isShared_33_ = v_isSharedCheck_49_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_newDecls_30_);
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
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_49_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint64_t v_tid_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_47_; 
v_tid_34_ = lean_ctor_get_uint64(v_traceState_21_, sizeof(void*)*1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_traceState_21_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_traceState_21_, 0);
lean_dec(v_unused_48_);
v___x_36_ = v_traceState_21_;
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
else
{
lean_dec(v_traceState_21_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_38_);
lean_ctor_set_uint64(v_reuseFailAlloc_46_, sizeof(void*)*1, v_tid_34_);
v___x_40_ = v_reuseFailAlloc_46_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 4, v___x_40_);
v___x_42_ = v___x_32_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_22_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_23_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v_ngen_24_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_25_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v_cache_26_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_messages_27_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_infoState_28_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_snapshotTasks_29_);
lean_ctor_set(v_reuseFailAlloc_45_, 9, v_newDecls_30_);
v___x_42_ = v_reuseFailAlloc_45_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_st_ref_set(v___y_15_, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_traces_19_);
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_50_);
lean_dec(v___y_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___boxed(lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(lean_object* v_opts_65_, lean_object* v_opt_66_){
_start:
{
lean_object* v_name_67_; lean_object* v_defValue_68_; lean_object* v_map_69_; lean_object* v___x_70_; 
v_name_67_ = lean_ctor_get(v_opt_66_, 0);
v_defValue_68_ = lean_ctor_get(v_opt_66_, 1);
v_map_69_ = lean_ctor_get(v_opts_65_, 0);
v___x_70_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_69_, v_name_67_);
if (lean_obj_tag(v___x_70_) == 0)
{
uint8_t v___x_71_; 
v___x_71_ = lean_unbox(v_defValue_68_);
return v___x_71_;
}
else
{
lean_object* v_val_72_; 
v_val_72_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v___x_70_);
if (lean_obj_tag(v_val_72_) == 1)
{
uint8_t v_v_73_; 
v_v_73_ = lean_ctor_get_uint8(v_val_72_, 0);
lean_dec_ref(v_val_72_);
return v_v_73_;
}
else
{
uint8_t v___x_74_; 
lean_dec(v_val_72_);
v___x_74_ = lean_unbox(v_defValue_68_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3___boxed(lean_object* v_opts_75_, lean_object* v_opt_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_75_, v_opt_76_);
lean_dec_ref(v_opt_76_);
lean_dec_ref(v_opts_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object* v_declName_79_, lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = l_Lean_MessageData_ofName(v_declName_79_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object* v_declName_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_mkCasesOn___lam__0(v_declName_88_, v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec_ref(v_x_89_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(lean_object* v_msgData_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; lean_object* v_env_103_; lean_object* v___x_104_; lean_object* v_mctx_105_; lean_object* v_lctx_106_; lean_object* v_options_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_102_ = lean_st_ref_get(v___y_100_);
v_env_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc_ref(v_env_103_);
lean_dec(v___x_102_);
v___x_104_ = lean_st_ref_get(v___y_98_);
v_mctx_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_mctx_105_);
lean_dec(v___x_104_);
v_lctx_106_ = lean_ctor_get(v___y_97_, 2);
v_options_107_ = lean_ctor_get(v___y_99_, 2);
lean_inc_ref(v_options_107_);
lean_inc_ref(v_lctx_106_);
v___x_108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_108_, 0, v_env_103_);
lean_ctor_set(v___x_108_, 1, v_mctx_105_);
lean_ctor_set(v___x_108_, 2, v_lctx_106_);
lean_ctor_set(v___x_108_, 3, v_options_107_);
v___x_109_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_msgData_96_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11___boxed(lean_object* v_msgData_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msgData_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_ref_124_; lean_object* v___x_125_; lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
v_ref_124_ = lean_ctor_get(v___y_121_, 5);
v___x_125_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msg_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_134_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_inc(v_ref_124_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_ref_124_);
lean_ctor_set(v___x_130_, 1, v_a_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 1);
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v_msg_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_box(0);
v___x_143_ = l_Lean_interruptExceptionId;
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg(){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object* v_ex_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; 
if (lean_obj_tag(v_ex_150_) == 16)
{
lean_object* v___x_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v___x_164_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
v___y_157_ = v___y_151_;
v___y_158_ = v___y_152_;
v___y_159_ = v___y_153_;
v___y_160_ = v___y_154_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v_options_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_options_161_ = lean_ctor_get(v___y_159_, 2);
lean_inc_ref(v_options_161_);
v___x_162_ = l_Lean_Kernel_Exception_toMessageData(v_ex_150_, v_options_161_);
v___x_163_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v___x_162_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_ex_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(lean_object* v_x_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v_x_180_);
v___x_187_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_a_186_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_187_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v_x_180_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v_x_180_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 0);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(size_t v_sz_203_, size_t v_i_204_, lean_object* v_bs_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_206_ == 0)
{
return v_bs_205_;
}
else
{
lean_object* v_v_207_; lean_object* v_msg_208_; lean_object* v___x_209_; lean_object* v_bs_x27_210_; size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v_v_207_ = lean_array_uget_borrowed(v_bs_205_, v_i_204_);
v_msg_208_ = lean_ctor_get(v_v_207_, 1);
lean_inc_ref(v_msg_208_);
v___x_209_ = lean_unsigned_to_nat(0u);
v_bs_x27_210_ = lean_array_uset(v_bs_205_, v_i_204_, v___x_209_);
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_add(v_i_204_, v___x_211_);
v___x_213_ = lean_array_uset(v_bs_x27_210_, v_i_204_, v_msg_208_);
v_i_204_ = v___x_212_;
v_bs_205_ = v___x_213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10___boxed(lean_object* v_sz_215_, lean_object* v_i_216_, lean_object* v_bs_217_){
_start:
{
size_t v_sz_boxed_218_; size_t v_i_boxed_219_; lean_object* v_res_220_; 
v_sz_boxed_218_ = lean_unbox_usize(v_sz_215_);
lean_dec(v_sz_215_);
v_i_boxed_219_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(v_sz_boxed_218_, v_i_boxed_219_, v_bs_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object* v_oldTraces_221_, lean_object* v_data_222_, lean_object* v_ref_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_fileName_230_; lean_object* v_fileMap_231_; lean_object* v_options_232_; lean_object* v_currRecDepth_233_; lean_object* v_maxRecDepth_234_; lean_object* v_ref_235_; lean_object* v_currNamespace_236_; lean_object* v_openDecls_237_; lean_object* v_initHeartbeats_238_; lean_object* v_maxHeartbeats_239_; lean_object* v_quotContext_240_; lean_object* v_currMacroScope_241_; uint8_t v_diag_242_; lean_object* v_cancelTk_x3f_243_; uint8_t v_suppressElabErrors_244_; lean_object* v_inheritedTraceOptions_245_; lean_object* v___x_246_; lean_object* v_traceState_247_; lean_object* v_traces_248_; lean_object* v_ref_249_; lean_object* v___x_250_; lean_object* v___x_251_; size_t v_sz_252_; size_t v___x_253_; lean_object* v___x_254_; lean_object* v_msg_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_295_; 
v_fileName_230_ = lean_ctor_get(v___y_227_, 0);
v_fileMap_231_ = lean_ctor_get(v___y_227_, 1);
v_options_232_ = lean_ctor_get(v___y_227_, 2);
v_currRecDepth_233_ = lean_ctor_get(v___y_227_, 3);
v_maxRecDepth_234_ = lean_ctor_get(v___y_227_, 4);
v_ref_235_ = lean_ctor_get(v___y_227_, 5);
v_currNamespace_236_ = lean_ctor_get(v___y_227_, 6);
v_openDecls_237_ = lean_ctor_get(v___y_227_, 7);
v_initHeartbeats_238_ = lean_ctor_get(v___y_227_, 8);
v_maxHeartbeats_239_ = lean_ctor_get(v___y_227_, 9);
v_quotContext_240_ = lean_ctor_get(v___y_227_, 10);
v_currMacroScope_241_ = lean_ctor_get(v___y_227_, 11);
v_diag_242_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*14);
v_cancelTk_x3f_243_ = lean_ctor_get(v___y_227_, 12);
v_suppressElabErrors_244_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_245_ = lean_ctor_get(v___y_227_, 13);
v___x_246_ = lean_st_ref_get(v___y_228_);
v_traceState_247_ = lean_ctor_get(v___x_246_, 4);
lean_inc_ref(v_traceState_247_);
lean_dec(v___x_246_);
v_traces_248_ = lean_ctor_get(v_traceState_247_, 0);
lean_inc_ref(v_traces_248_);
lean_dec_ref(v_traceState_247_);
v_ref_249_ = l_Lean_replaceRef(v_ref_223_, v_ref_235_);
lean_inc_ref(v_inheritedTraceOptions_245_);
lean_inc(v_cancelTk_x3f_243_);
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
lean_inc(v_maxHeartbeats_239_);
lean_inc(v_initHeartbeats_238_);
lean_inc(v_openDecls_237_);
lean_inc(v_currNamespace_236_);
lean_inc(v_maxRecDepth_234_);
lean_inc(v_currRecDepth_233_);
lean_inc_ref(v_options_232_);
lean_inc_ref(v_fileMap_231_);
lean_inc_ref(v_fileName_230_);
v___x_250_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_250_, 0, v_fileName_230_);
lean_ctor_set(v___x_250_, 1, v_fileMap_231_);
lean_ctor_set(v___x_250_, 2, v_options_232_);
lean_ctor_set(v___x_250_, 3, v_currRecDepth_233_);
lean_ctor_set(v___x_250_, 4, v_maxRecDepth_234_);
lean_ctor_set(v___x_250_, 5, v_ref_249_);
lean_ctor_set(v___x_250_, 6, v_currNamespace_236_);
lean_ctor_set(v___x_250_, 7, v_openDecls_237_);
lean_ctor_set(v___x_250_, 8, v_initHeartbeats_238_);
lean_ctor_set(v___x_250_, 9, v_maxHeartbeats_239_);
lean_ctor_set(v___x_250_, 10, v_quotContext_240_);
lean_ctor_set(v___x_250_, 11, v_currMacroScope_241_);
lean_ctor_set(v___x_250_, 12, v_cancelTk_x3f_243_);
lean_ctor_set(v___x_250_, 13, v_inheritedTraceOptions_245_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*14, v_diag_242_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*14 + 1, v_suppressElabErrors_244_);
v___x_251_ = l_Lean_PersistentArray_toArray___redArg(v_traces_248_);
lean_dec_ref(v_traces_248_);
v_sz_252_ = lean_array_size(v___x_251_);
v___x_253_ = ((size_t)0ULL);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__10(v_sz_252_, v___x_253_, v___x_251_);
v_msg_255_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_255_, 0, v_data_222_);
lean_ctor_set(v_msg_255_, 1, v_msg_224_);
lean_ctor_set(v_msg_255_, 2, v___x_254_);
v___x_256_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7_spec__11(v_msg_255_, v___y_225_, v___y_226_, v___x_250_, v___y_228_);
lean_dec_ref(v___x_250_);
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
lean_object* v___x_261_; lean_object* v_traceState_262_; lean_object* v_env_263_; lean_object* v_nextMacroScope_264_; lean_object* v_ngen_265_; lean_object* v_auxDeclNGen_266_; lean_object* v_cache_267_; lean_object* v_messages_268_; lean_object* v_infoState_269_; lean_object* v_snapshotTasks_270_; lean_object* v_newDecls_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v___x_261_ = lean_st_ref_take(v___y_228_);
v_traceState_262_ = lean_ctor_get(v___x_261_, 4);
v_env_263_ = lean_ctor_get(v___x_261_, 0);
v_nextMacroScope_264_ = lean_ctor_get(v___x_261_, 1);
v_ngen_265_ = lean_ctor_get(v___x_261_, 2);
v_auxDeclNGen_266_ = lean_ctor_get(v___x_261_, 3);
v_cache_267_ = lean_ctor_get(v___x_261_, 5);
v_messages_268_ = lean_ctor_get(v___x_261_, 6);
v_infoState_269_ = lean_ctor_get(v___x_261_, 7);
v_snapshotTasks_270_ = lean_ctor_get(v___x_261_, 8);
v_newDecls_271_ = lean_ctor_get(v___x_261_, 9);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v___x_261_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_newDecls_271_);
lean_inc(v_snapshotTasks_270_);
lean_inc(v_infoState_269_);
lean_inc(v_messages_268_);
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
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_ref_223_);
lean_ctor_set(v___x_279_, 1, v_a_257_);
v___x_280_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_221_, v___x_279_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_280_);
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_280_);
lean_ctor_set_uint64(v_reuseFailAlloc_291_, sizeof(void*)*1, v_tid_275_);
v___x_282_ = v_reuseFailAlloc_291_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v___x_282_);
v___x_284_ = v___x_273_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_env_263_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_nextMacroScope_264_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_ngen_265_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_auxDeclNGen_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_cache_267_);
lean_ctor_set(v_reuseFailAlloc_290_, 6, v_messages_268_);
lean_ctor_set(v_reuseFailAlloc_290_, 7, v_infoState_269_);
lean_ctor_set(v_reuseFailAlloc_290_, 8, v_snapshotTasks_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 9, v_newDecls_271_);
v___x_284_ = v_reuseFailAlloc_290_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = lean_st_ref_set(v___y_228_, v___x_284_);
v___x_286_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_286_);
v___x_288_ = v___x_259_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object* v_oldTraces_296_, lean_object* v_data_297_, lean_object* v_ref_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_oldTraces_296_, v_data_297_, v_ref_298_, v_msg_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v_x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v_x_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v_x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 1);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v_x_306_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v_x_306_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_x_306_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 0);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg___boxed(lean_object* v_x_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_x_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object* v_opts_327_, lean_object* v_opt_328_){
_start:
{
lean_object* v_name_329_; lean_object* v_defValue_330_; lean_object* v_map_331_; lean_object* v___x_332_; 
v_name_329_ = lean_ctor_get(v_opt_328_, 0);
v_defValue_330_ = lean_ctor_get(v_opt_328_, 1);
v_map_331_ = lean_ctor_get(v_opts_327_, 0);
v___x_332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_331_, v_name_329_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_inc(v_defValue_330_);
return v_defValue_330_;
}
else
{
lean_object* v_val_333_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v_val_333_) == 3)
{
lean_object* v_v_334_; 
v_v_334_ = lean_ctor_get(v_val_333_, 0);
lean_inc(v_v_334_);
lean_dec_ref(v_val_333_);
return v_v_334_;
}
else
{
lean_dec(v_val_333_);
lean_inc(v_defValue_330_);
return v_defValue_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object* v_opts_335_, lean_object* v_opt_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_335_, v_opt_336_);
lean_dec_ref(v_opt_336_);
lean_dec_ref(v_opts_335_);
return v_res_337_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object* v_e_338_){
_start:
{
if (lean_obj_tag(v_e_338_) == 0)
{
uint8_t v___x_339_; 
v___x_339_ = 2;
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object* v_e_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_e_341_);
lean_dec_ref(v_e_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0));
v___x_346_ = l_Lean_stringToMessageData(v___x_345_);
return v___x_346_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2(void){
_start:
{
lean_object* v___x_347_; double v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_float_of_nat(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5(void){
_start:
{
lean_object* v___x_352_; double v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1000u);
v___x_353_ = lean_float_of_nat(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object* v_cls_354_, uint8_t v_collapsed_355_, lean_object* v_tag_356_, lean_object* v_opts_357_, uint8_t v_clsEnabled_358_, lean_object* v_oldTraces_359_, lean_object* v_msg_360_, lean_object* v_resStartStop_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_fst_367_; lean_object* v_snd_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_459_; 
v_fst_367_ = lean_ctor_get(v_resStartStop_361_, 0);
v_snd_368_ = lean_ctor_get(v_resStartStop_361_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_resStartStop_361_);
if (v_isSharedCheck_459_ == 0)
{
v___x_370_ = v_resStartStop_361_;
v_isShared_371_ = v_isSharedCheck_459_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snd_368_);
lean_inc(v_fst_367_);
lean_dec(v_resStartStop_361_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_459_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v_data_375_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_458_; 
v_fst_378_ = lean_ctor_get(v_snd_368_, 0);
v_snd_379_ = lean_ctor_get(v_snd_368_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_snd_368_);
if (v_isSharedCheck_458_ == 0)
{
v___x_381_ = v_snd_368_;
v_isShared_382_ = v_isSharedCheck_458_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_snd_368_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_458_;
goto v_resetjp_380_;
}
v___jp_372_:
{
lean_object* v___x_376_; 
lean_inc(v___y_373_);
v___x_376_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_oldTraces_359_, v_data_375_, v___y_373_, v___y_374_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_376_);
v___x_377_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_fst_367_);
return v___x_377_;
}
else
{
lean_dec(v_fst_367_);
return v___x_376_;
}
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___y_386_; lean_object* v_a_387_; uint8_t v___y_411_; double v___y_443_; 
v___x_383_ = l_Lean_trace_profiler;
v___x_384_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_357_, v___x_383_);
if (v___x_384_ == 0)
{
v___y_411_ = v___x_384_;
goto v___jp_410_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = l_Lean_trace_profiler_useHeartbeats;
v___x_449_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_357_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; double v___x_452_; double v___x_453_; double v___x_454_; 
v___x_450_ = l_Lean_trace_profiler_threshold;
v___x_451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_357_, v___x_450_);
v___x_452_ = lean_float_of_nat(v___x_451_);
v___x_453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__5);
v___x_454_ = lean_float_div(v___x_452_, v___x_453_);
v___y_443_ = v___x_454_;
goto v___jp_442_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; 
v___x_455_ = l_Lean_trace_profiler_threshold;
v___x_456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_357_, v___x_455_);
v___x_457_ = lean_float_of_nat(v___x_456_);
v___y_443_ = v___x_457_;
goto v___jp_442_;
}
}
v___jp_385_:
{
uint8_t v_result_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_result_388_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_fst_367_);
v___x_389_ = l_Lean_TraceResult_toEmoji(v_result_388_);
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
v___x_391_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 7);
lean_ctor_set(v___x_381_, 1, v___x_391_);
lean_ctor_set(v___x_381_, 0, v___x_390_);
v___x_393_ = v___x_381_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_404_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v_m_395_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 7);
lean_ctor_set(v___x_370_, 1, v_a_387_);
lean_ctor_set(v___x_370_, 0, v___x_393_);
v_m_395_ = v___x_370_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_387_);
v_m_395_ = v_reuseFailAlloc_403_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; double v___x_398_; lean_object* v_data_399_; 
v___x_396_ = lean_box(v_result_388_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2);
lean_inc_ref(v_tag_356_);
lean_inc_ref(v___x_397_);
lean_inc(v_cls_354_);
v_data_399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_399_, 0, v_cls_354_);
lean_ctor_set(v_data_399_, 1, v___x_397_);
lean_ctor_set(v_data_399_, 2, v_tag_356_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3, v___x_398_);
lean_ctor_set_float(v_data_399_, sizeof(void*)*3 + 8, v___x_398_);
lean_ctor_set_uint8(v_data_399_, sizeof(void*)*3 + 16, v_collapsed_355_);
if (v___x_384_ == 0)
{
lean_dec_ref(v___x_397_);
lean_dec(v_snd_379_);
lean_dec(v_fst_378_);
lean_dec_ref(v_tag_356_);
lean_dec(v_cls_354_);
v___y_373_ = v___y_386_;
v___y_374_ = v_m_395_;
v_data_375_ = v_data_399_;
goto v___jp_372_;
}
else
{
lean_object* v_data_400_; double v___x_401_; double v___x_402_; 
lean_dec_ref(v_data_399_);
v_data_400_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_400_, 0, v_cls_354_);
lean_ctor_set(v_data_400_, 1, v___x_397_);
lean_ctor_set(v_data_400_, 2, v_tag_356_);
v___x_401_ = lean_unbox_float(v_fst_378_);
lean_dec(v_fst_378_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3, v___x_401_);
v___x_402_ = lean_unbox_float(v_snd_379_);
lean_dec(v_snd_379_);
lean_ctor_set_float(v_data_400_, sizeof(void*)*3 + 8, v___x_402_);
lean_ctor_set_uint8(v_data_400_, sizeof(void*)*3 + 16, v_collapsed_355_);
v___y_373_ = v___y_386_;
v___y_374_ = v_m_395_;
v_data_375_ = v_data_400_;
goto v___jp_372_;
}
}
}
}
v___jp_405_:
{
lean_object* v_ref_406_; lean_object* v___x_407_; 
v_ref_406_ = lean_ctor_get(v___y_364_, 5);
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v_fst_367_);
v___x_407_ = lean_apply_6(v_msg_360_, v_fst_367_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, lean_box(0));
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v___y_386_ = v_ref_406_;
v_a_387_ = v_a_408_;
goto v___jp_385_;
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__4);
v___y_386_ = v_ref_406_;
v_a_387_ = v___x_409_;
goto v___jp_385_;
}
}
v___jp_410_:
{
if (v_clsEnabled_358_ == 0)
{
if (v___y_411_ == 0)
{
lean_object* v___x_412_; lean_object* v_traceState_413_; lean_object* v_env_414_; lean_object* v_nextMacroScope_415_; lean_object* v_ngen_416_; lean_object* v_auxDeclNGen_417_; lean_object* v_cache_418_; lean_object* v_messages_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v_newDecls_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_381_);
lean_dec(v_snd_379_);
lean_dec(v_fst_378_);
lean_del_object(v___x_370_);
lean_dec_ref(v_msg_360_);
lean_dec_ref(v_tag_356_);
lean_dec(v_cls_354_);
v___x_412_ = lean_st_ref_take(v___y_365_);
v_traceState_413_ = lean_ctor_get(v___x_412_, 4);
v_env_414_ = lean_ctor_get(v___x_412_, 0);
v_nextMacroScope_415_ = lean_ctor_get(v___x_412_, 1);
v_ngen_416_ = lean_ctor_get(v___x_412_, 2);
v_auxDeclNGen_417_ = lean_ctor_get(v___x_412_, 3);
v_cache_418_ = lean_ctor_get(v___x_412_, 5);
v_messages_419_ = lean_ctor_get(v___x_412_, 6);
v_infoState_420_ = lean_ctor_get(v___x_412_, 7);
v_snapshotTasks_421_ = lean_ctor_get(v___x_412_, 8);
v_newDecls_422_ = lean_ctor_get(v___x_412_, 9);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_441_ == 0)
{
v___x_424_ = v___x_412_;
v_isShared_425_ = v_isSharedCheck_441_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_newDecls_422_);
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_messages_419_);
lean_inc(v_cache_418_);
lean_inc(v_traceState_413_);
lean_inc(v_auxDeclNGen_417_);
lean_inc(v_ngen_416_);
lean_inc(v_nextMacroScope_415_);
lean_inc(v_env_414_);
lean_dec(v___x_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_441_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint64_t v_tid_426_; lean_object* v_traces_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_440_; 
v_tid_426_ = lean_ctor_get_uint64(v_traceState_413_, sizeof(void*)*1);
v_traces_427_ = lean_ctor_get(v_traceState_413_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_traceState_413_);
if (v_isSharedCheck_440_ == 0)
{
v___x_429_ = v_traceState_413_;
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_traces_427_);
lean_dec(v_traceState_413_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_359_, v_traces_427_);
lean_dec_ref(v_traces_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_431_);
lean_ctor_set_uint64(v_reuseFailAlloc_439_, sizeof(void*)*1, v_tid_426_);
v___x_433_ = v_reuseFailAlloc_439_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v___x_433_);
v___x_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_env_414_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_nextMacroScope_415_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_ngen_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_auxDeclNGen_417_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_cache_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_messages_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_snapshotTasks_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 9, v_newDecls_422_);
v___x_435_ = v_reuseFailAlloc_438_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_st_ref_set(v___y_365_, v___x_435_);
v___x_437_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_fst_367_);
return v___x_437_;
}
}
}
}
}
else
{
goto v___jp_405_;
}
}
else
{
goto v___jp_405_;
}
}
v___jp_442_:
{
double v___x_444_; double v___x_445_; double v___x_446_; uint8_t v___x_447_; 
v___x_444_ = lean_unbox_float(v_snd_379_);
v___x_445_ = lean_unbox_float(v_fst_378_);
v___x_446_ = lean_float_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_float_decLt(v___y_443_, v___x_446_);
v___y_411_ = v___x_447_;
goto v___jp_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_cls_460_, lean_object* v_collapsed_461_, lean_object* v_tag_462_, lean_object* v_opts_463_, lean_object* v_clsEnabled_464_, lean_object* v_oldTraces_465_, lean_object* v_msg_466_, lean_object* v_resStartStop_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v_collapsed_boxed_473_; uint8_t v_clsEnabled_boxed_474_; lean_object* v_res_475_; 
v_collapsed_boxed_473_ = lean_unbox(v_collapsed_461_);
v_clsEnabled_boxed_474_ = lean_unbox(v_clsEnabled_464_);
v_res_475_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v_cls_460_, v_collapsed_boxed_473_, v_tag_462_, v_opts_463_, v_clsEnabled_boxed_474_, v_oldTraces_465_, v_msg_466_, v_resStartStop_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_opts_463_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_476_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
lean_ctor_set(v___x_482_, 3, v___x_481_);
lean_ctor_set(v___x_482_, 4, v___x_481_);
lean_ctor_set(v___x_482_, 5, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object* v_declName_483_, uint8_t v_s_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; lean_object* v_env_489_; lean_object* v_nextMacroScope_490_; lean_object* v_ngen_491_; lean_object* v_auxDeclNGen_492_; lean_object* v_traceState_493_; lean_object* v_messages_494_; lean_object* v_infoState_495_; lean_object* v_snapshotTasks_496_; lean_object* v_newDecls_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_526_; 
v___x_488_ = lean_st_ref_take(v___y_486_);
v_env_489_ = lean_ctor_get(v___x_488_, 0);
v_nextMacroScope_490_ = lean_ctor_get(v___x_488_, 1);
v_ngen_491_ = lean_ctor_get(v___x_488_, 2);
v_auxDeclNGen_492_ = lean_ctor_get(v___x_488_, 3);
v_traceState_493_ = lean_ctor_get(v___x_488_, 4);
v_messages_494_ = lean_ctor_get(v___x_488_, 6);
v_infoState_495_ = lean_ctor_get(v___x_488_, 7);
v_snapshotTasks_496_ = lean_ctor_get(v___x_488_, 8);
v_newDecls_497_ = lean_ctor_get(v___x_488_, 9);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_488_, 5);
lean_dec(v_unused_527_);
v___x_499_ = v___x_488_;
v_isShared_500_ = v_isSharedCheck_526_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_newDecls_497_);
lean_inc(v_snapshotTasks_496_);
lean_inc(v_infoState_495_);
lean_inc(v_messages_494_);
lean_inc(v_traceState_493_);
lean_inc(v_auxDeclNGen_492_);
lean_inc(v_ngen_491_);
lean_inc(v_nextMacroScope_490_);
lean_inc(v_env_489_);
lean_dec(v___x_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_526_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_501_ = 0;
v___x_502_ = lean_box(0);
v___x_503_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_489_, v_declName_483_, v_s_484_, v___x_501_, v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 5, v___x_504_);
lean_ctor_set(v___x_499_, 0, v___x_503_);
v___x_506_ = v___x_499_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_nextMacroScope_490_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_ngen_491_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_auxDeclNGen_492_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_traceState_493_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_messages_494_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_infoState_495_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v_snapshotTasks_496_);
lean_ctor_set(v_reuseFailAlloc_525_, 9, v_newDecls_497_);
v___x_506_ = v_reuseFailAlloc_525_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_mctx_509_; lean_object* v_zetaDeltaFVarIds_510_; lean_object* v_postponed_511_; lean_object* v_diag_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_523_; 
v___x_507_ = lean_st_ref_set(v___y_486_, v___x_506_);
v___x_508_ = lean_st_ref_take(v___y_485_);
v_mctx_509_ = lean_ctor_get(v___x_508_, 0);
v_zetaDeltaFVarIds_510_ = lean_ctor_get(v___x_508_, 2);
v_postponed_511_ = lean_ctor_get(v___x_508_, 3);
v_diag_512_ = lean_ctor_get(v___x_508_, 4);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_508_, 1);
lean_dec(v_unused_524_);
v___x_514_ = v___x_508_;
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_diag_512_);
lean_inc(v_postponed_511_);
lean_inc(v_zetaDeltaFVarIds_510_);
lean_inc(v_mctx_509_);
lean_dec(v___x_508_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_mctx_509_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_zetaDeltaFVarIds_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_postponed_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_diag_512_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_st_ref_set(v___y_485_, v___x_518_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_declName_528_, lean_object* v_s_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v_s_boxed_533_; lean_object* v_res_534_; 
v_s_boxed_533_ = lean_unbox(v_s_529_);
v_res_534_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_528_, v_s_boxed_533_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec(v___y_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(lean_object* v_declName_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_541_ = 0;
v___x_542_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_535_, v___x_541_, v___y_537_, v___y_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_declName_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_declName_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
static lean_object* _init_l_Lean_mkCasesOn___closed__6(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_560_ = ((lean_object*)(l_Lean_mkCasesOn___closed__5));
v___x_561_ = l_Lean_Name_append(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static double _init_l_Lean_mkCasesOn___closed__7(void){
_start:
{
lean_object* v___x_562_; double v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1000000000u);
v___x_563_ = lean_float_of_nat(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_options_570_; lean_object* v_inheritedTraceOptions_571_; uint8_t v_hasTrace_572_; lean_object* v_name_573_; 
v_options_570_ = lean_ctor_get(v_a_567_, 2);
v_inheritedTraceOptions_571_ = lean_ctor_get(v_a_567_, 13);
v_hasTrace_572_ = lean_ctor_get_uint8(v_options_570_, sizeof(void*)*1);
lean_inc(v_declName_564_);
v_name_573_ = l_Lean_mkCasesOnName(v_declName_564_);
if (v_hasTrace_572_ == 0)
{
lean_object* v___x_574_; lean_object* v_env_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = lean_st_ref_get(v_a_568_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_574_);
v___x_576_ = lean_elab_environment_to_kernel_env(v_env_575_);
v___x_577_ = lean_mk_cases_on(v___x_576_, v_declName_564_);
lean_dec(v_declName_564_);
v___x_578_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_577_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = l_Lean_addDecl(v_a_579_, v_hasTrace_572_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_env_583_; lean_object* v_nextMacroScope_584_; lean_object* v_ngen_585_; lean_object* v_auxDeclNGen_586_; lean_object* v_traceState_587_; lean_object* v_messages_588_; lean_object* v_infoState_589_; lean_object* v_snapshotTasks_590_; lean_object* v_newDecls_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___x_580_);
lean_inc(v_name_573_);
v___x_581_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_573_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec_ref(v___x_581_);
v___x_582_ = lean_st_ref_take(v_a_568_);
v_env_583_ = lean_ctor_get(v___x_582_, 0);
v_nextMacroScope_584_ = lean_ctor_get(v___x_582_, 1);
v_ngen_585_ = lean_ctor_get(v___x_582_, 2);
v_auxDeclNGen_586_ = lean_ctor_get(v___x_582_, 3);
v_traceState_587_ = lean_ctor_get(v___x_582_, 4);
v_messages_588_ = lean_ctor_get(v___x_582_, 6);
v_infoState_589_ = lean_ctor_get(v___x_582_, 7);
v_snapshotTasks_590_ = lean_ctor_get(v___x_582_, 8);
v_newDecls_591_ = lean_ctor_get(v___x_582_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_582_, 5);
lean_dec(v_unused_618_);
v___x_593_ = v___x_582_;
v_isShared_594_ = v_isSharedCheck_617_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_newDecls_591_);
lean_inc(v_snapshotTasks_590_);
lean_inc(v_infoState_589_);
lean_inc(v_messages_588_);
lean_inc(v_traceState_587_);
lean_inc(v_auxDeclNGen_586_);
lean_inc(v_ngen_585_);
lean_inc(v_nextMacroScope_584_);
lean_inc(v_env_583_);
lean_dec(v___x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_617_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
lean_inc(v_name_573_);
v___x_595_ = l_Lean_markAuxRecursor(v_env_583_, v_name_573_);
v___x_596_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 5, v___x_596_);
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_584_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_585_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_586_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_587_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_messages_588_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_infoState_589_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_snapshotTasks_590_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_newDecls_591_);
v___x_598_ = v_reuseFailAlloc_616_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_mctx_601_; lean_object* v_zetaDeltaFVarIds_602_; lean_object* v_postponed_603_; lean_object* v_diag_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
v___x_599_ = lean_st_ref_set(v_a_568_, v___x_598_);
v___x_600_ = lean_st_ref_take(v_a_566_);
v_mctx_601_ = lean_ctor_get(v___x_600_, 0);
v_zetaDeltaFVarIds_602_ = lean_ctor_get(v___x_600_, 2);
v_postponed_603_ = lean_ctor_get(v___x_600_, 3);
v_diag_604_ = lean_ctor_get(v___x_600_, 4);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_600_, 1);
lean_dec(v_unused_615_);
v___x_606_ = v___x_600_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_diag_604_);
lean_inc(v_postponed_603_);
lean_inc(v_zetaDeltaFVarIds_602_);
lean_inc(v_mctx_601_);
lean_dec(v___x_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_mctx_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_zetaDeltaFVarIds_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_postponed_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_diag_604_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_set(v_a_566_, v___x_610_);
v___x_612_ = l_Lean_enableRealizationsForConst(v_name_573_, v_a_567_, v_a_568_);
return v___x_612_;
}
}
}
}
}
else
{
lean_dec(v_name_573_);
return v___x_580_;
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_name_573_);
v_a_619_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_578_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_578_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v_a_635_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_a_650_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v_a_668_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v_a_680_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; 
lean_inc(v_declName_564_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_627_, 0, v_declName_564_);
v___x_628_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_629_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_630_ = lean_obj_once(&l_Lean_mkCasesOn___closed__6, &l_Lean_mkCasesOn___closed__6_once, _init_l_Lean_mkCasesOn___closed__6);
v___x_631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_571_, v_options_570_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = l_Lean_trace_profiler;
v___x_796_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_570_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v_env_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v___f_627_);
v___x_797_ = lean_st_ref_get(v_a_568_);
v_env_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_env_798_);
lean_dec(v___x_797_);
v___x_799_ = lean_elab_environment_to_kernel_env(v_env_798_);
v___x_800_ = lean_mk_cases_on(v___x_799_, v_declName_564_);
lean_dec(v_declName_564_);
v___x_801_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_800_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = l_Lean_addDecl(v_a_802_, v___x_796_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_env_806_; lean_object* v_nextMacroScope_807_; lean_object* v_ngen_808_; lean_object* v_auxDeclNGen_809_; lean_object* v_traceState_810_; lean_object* v_messages_811_; lean_object* v_infoState_812_; lean_object* v_snapshotTasks_813_; lean_object* v_newDecls_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v___x_803_);
lean_inc(v_name_573_);
v___x_804_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_573_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec_ref(v___x_804_);
v___x_805_ = lean_st_ref_take(v_a_568_);
v_env_806_ = lean_ctor_get(v___x_805_, 0);
v_nextMacroScope_807_ = lean_ctor_get(v___x_805_, 1);
v_ngen_808_ = lean_ctor_get(v___x_805_, 2);
v_auxDeclNGen_809_ = lean_ctor_get(v___x_805_, 3);
v_traceState_810_ = lean_ctor_get(v___x_805_, 4);
v_messages_811_ = lean_ctor_get(v___x_805_, 6);
v_infoState_812_ = lean_ctor_get(v___x_805_, 7);
v_snapshotTasks_813_ = lean_ctor_get(v___x_805_, 8);
v_newDecls_814_ = lean_ctor_get(v___x_805_, 9);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_805_, 5);
lean_dec(v_unused_841_);
v___x_816_ = v___x_805_;
v_isShared_817_ = v_isSharedCheck_840_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_newDecls_814_);
lean_inc(v_snapshotTasks_813_);
lean_inc(v_infoState_812_);
lean_inc(v_messages_811_);
lean_inc(v_traceState_810_);
lean_inc(v_auxDeclNGen_809_);
lean_inc(v_ngen_808_);
lean_inc(v_nextMacroScope_807_);
lean_inc(v_env_806_);
lean_dec(v___x_805_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_840_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_name_573_);
v___x_818_ = l_Lean_markAuxRecursor(v_env_806_, v_name_573_);
v___x_819_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 5, v___x_819_);
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_821_ = v___x_816_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_nextMacroScope_807_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_ngen_808_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_auxDeclNGen_809_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_traceState_810_);
lean_ctor_set(v_reuseFailAlloc_839_, 5, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 6, v_messages_811_);
lean_ctor_set(v_reuseFailAlloc_839_, 7, v_infoState_812_);
lean_ctor_set(v_reuseFailAlloc_839_, 8, v_snapshotTasks_813_);
lean_ctor_set(v_reuseFailAlloc_839_, 9, v_newDecls_814_);
v___x_821_ = v_reuseFailAlloc_839_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_mctx_824_; lean_object* v_zetaDeltaFVarIds_825_; lean_object* v_postponed_826_; lean_object* v_diag_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v___x_822_ = lean_st_ref_set(v_a_568_, v___x_821_);
v___x_823_ = lean_st_ref_take(v_a_566_);
v_mctx_824_ = lean_ctor_get(v___x_823_, 0);
v_zetaDeltaFVarIds_825_ = lean_ctor_get(v___x_823_, 2);
v_postponed_826_ = lean_ctor_get(v___x_823_, 3);
v_diag_827_ = lean_ctor_get(v___x_823_, 4);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_823_, 1);
lean_dec(v_unused_838_);
v___x_829_ = v___x_823_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_diag_827_);
lean_inc(v_postponed_826_);
lean_inc(v_zetaDeltaFVarIds_825_);
lean_inc(v_mctx_824_);
lean_dec(v___x_823_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_mctx_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_zetaDeltaFVarIds_825_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_postponed_826_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_diag_827_);
v___x_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_st_ref_set(v_a_566_, v___x_833_);
v___x_835_ = l_Lean_enableRealizationsForConst(v_name_573_, v_a_567_, v_a_568_);
return v___x_835_;
}
}
}
}
}
else
{
lean_dec(v_name_573_);
return v___x_803_;
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_name_573_);
v_a_842_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_801_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_801_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
goto v___jp_695_;
}
}
else
{
goto v___jp_695_;
}
v___jp_632_:
{
lean_object* v___x_636_; double v___x_637_; double v___x_638_; double v___x_639_; double v___x_640_; double v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_636_ = lean_io_mono_nanos_now();
v___x_637_ = lean_float_of_nat(v___y_634_);
v___x_638_ = lean_float_once(&l_Lean_mkCasesOn___closed__7, &l_Lean_mkCasesOn___closed__7_once, _init_l_Lean_mkCasesOn___closed__7);
v___x_639_ = lean_float_div(v___x_637_, v___x_638_);
v___x_640_ = lean_float_of_nat(v___x_636_);
v___x_641_ = lean_float_div(v___x_640_, v___x_638_);
v___x_642_ = lean_box_float(v___x_639_);
v___x_643_ = lean_box_float(v___x_641_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_635_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_628_, v_hasTrace_572_, v___x_629_, v_options_570_, v___x_631_, v___y_633_, v___f_627_, v___x_645_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_646_;
}
v___jp_647_:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v_a_650_);
v___y_633_ = v___y_648_;
v___y_634_ = v___y_649_;
v_a_635_ = v___x_651_;
goto v___jp_632_;
}
v___jp_652_:
{
if (lean_obj_tag(v___y_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___y_655_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___y_655_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___y_655_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___y_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v___y_633_ = v___y_653_;
v___y_634_ = v___y_654_;
v_a_635_ = v___x_661_;
goto v___jp_632_;
}
}
}
else
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___y_655_, 0);
lean_inc(v_a_664_);
lean_dec_ref(v___y_655_);
v___y_648_ = v___y_653_;
v___y_649_ = v___y_654_;
v_a_650_ = v_a_664_;
goto v___jp_647_;
}
}
v___jp_665_:
{
lean_object* v___x_669_; double v___x_670_; double v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_669_ = lean_io_get_num_heartbeats();
v___x_670_ = lean_float_of_nat(v___y_667_);
v___x_671_ = lean_float_of_nat(v___x_669_);
v___x_672_ = lean_box_float(v___x_670_);
v___x_673_ = lean_box_float(v___x_671_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_668_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_628_, v_hasTrace_572_, v___x_629_, v_options_570_, v___x_631_, v___y_666_, v___f_627_, v___x_675_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_676_;
}
v___jp_677_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_a_680_);
v___y_666_ = v___y_678_;
v___y_667_ = v___y_679_;
v_a_668_ = v___x_681_;
goto v___jp_665_;
}
v___jp_682_:
{
if (lean_obj_tag(v___y_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___y_685_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___y_685_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___y_685_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___y_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v___y_666_ = v___y_683_;
v___y_667_ = v___y_684_;
v_a_668_ = v___x_691_;
goto v___jp_665_;
}
}
}
else
{
lean_object* v_a_694_; 
v_a_694_ = lean_ctor_get(v___y_685_, 0);
lean_inc(v_a_694_);
lean_dec_ref(v___y_685_);
v___y_678_ = v___y_683_;
v___y_679_ = v___y_684_;
v_a_680_ = v_a_694_;
goto v___jp_677_;
}
}
v___jp_695_:
{
lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_696_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v_a_568_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
v___x_698_ = l_Lean_trace_profiler_useHeartbeats;
v___x_699_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_570_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_env_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = lean_io_mono_nanos_now();
v___x_701_ = lean_st_ref_get(v_a_568_);
v_env_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_ref(v_env_702_);
lean_dec(v___x_701_);
v___x_703_ = lean_elab_environment_to_kernel_env(v_env_702_);
v___x_704_ = lean_mk_cases_on(v___x_703_, v_declName_564_);
lean_dec(v_declName_564_);
v___x_705_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_704_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = l_Lean_addDecl(v_a_706_, v___x_699_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_env_710_; lean_object* v_nextMacroScope_711_; lean_object* v_ngen_712_; lean_object* v_auxDeclNGen_713_; lean_object* v_traceState_714_; lean_object* v_messages_715_; lean_object* v_infoState_716_; lean_object* v_snapshotTasks_717_; lean_object* v_newDecls_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___x_707_);
lean_inc(v_name_573_);
v___x_708_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_573_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec_ref(v___x_708_);
v___x_709_ = lean_st_ref_take(v_a_568_);
v_env_710_ = lean_ctor_get(v___x_709_, 0);
v_nextMacroScope_711_ = lean_ctor_get(v___x_709_, 1);
v_ngen_712_ = lean_ctor_get(v___x_709_, 2);
v_auxDeclNGen_713_ = lean_ctor_get(v___x_709_, 3);
v_traceState_714_ = lean_ctor_get(v___x_709_, 4);
v_messages_715_ = lean_ctor_get(v___x_709_, 6);
v_infoState_716_ = lean_ctor_get(v___x_709_, 7);
v_snapshotTasks_717_ = lean_ctor_get(v___x_709_, 8);
v_newDecls_718_ = lean_ctor_get(v___x_709_, 9);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_709_, 5);
lean_dec(v_unused_745_);
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_744_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_newDecls_718_);
lean_inc(v_snapshotTasks_717_);
lean_inc(v_infoState_716_);
lean_inc(v_messages_715_);
lean_inc(v_traceState_714_);
lean_inc(v_auxDeclNGen_713_);
lean_inc(v_ngen_712_);
lean_inc(v_nextMacroScope_711_);
lean_inc(v_env_710_);
lean_dec(v___x_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_744_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_inc(v_name_573_);
v___x_722_ = l_Lean_markAuxRecursor(v_env_710_, v_name_573_);
v___x_723_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 5, v___x_723_);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_nextMacroScope_711_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_ngen_712_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_auxDeclNGen_713_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_traceState_714_);
lean_ctor_set(v_reuseFailAlloc_743_, 5, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_743_, 6, v_messages_715_);
lean_ctor_set(v_reuseFailAlloc_743_, 7, v_infoState_716_);
lean_ctor_set(v_reuseFailAlloc_743_, 8, v_snapshotTasks_717_);
lean_ctor_set(v_reuseFailAlloc_743_, 9, v_newDecls_718_);
v___x_725_ = v_reuseFailAlloc_743_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_mctx_728_; lean_object* v_zetaDeltaFVarIds_729_; lean_object* v_postponed_730_; lean_object* v_diag_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v___x_726_ = lean_st_ref_set(v_a_568_, v___x_725_);
v___x_727_ = lean_st_ref_take(v_a_566_);
v_mctx_728_ = lean_ctor_get(v___x_727_, 0);
v_zetaDeltaFVarIds_729_ = lean_ctor_get(v___x_727_, 2);
v_postponed_730_ = lean_ctor_get(v___x_727_, 3);
v_diag_731_ = lean_ctor_get(v___x_727_, 4);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_727_, 1);
lean_dec(v_unused_742_);
v___x_733_ = v___x_727_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_diag_731_);
lean_inc(v_postponed_730_);
lean_inc(v_zetaDeltaFVarIds_729_);
lean_inc(v_mctx_728_);
lean_dec(v___x_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_mctx_728_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_zetaDeltaFVarIds_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_postponed_730_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_diag_731_);
v___x_737_ = v_reuseFailAlloc_740_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_st_ref_set(v_a_566_, v___x_737_);
v___x_739_ = l_Lean_enableRealizationsForConst(v_name_573_, v_a_567_, v_a_568_);
v___y_653_ = v_a_697_;
v___y_654_ = v___x_700_;
v___y_655_ = v___x_739_;
goto v___jp_652_;
}
}
}
}
}
else
{
lean_dec(v_name_573_);
v___y_653_ = v_a_697_;
v___y_654_ = v___x_700_;
v___y_655_ = v___x_707_;
goto v___jp_652_;
}
}
else
{
lean_object* v_a_746_; 
lean_dec(v_name_573_);
v_a_746_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_705_);
v___y_648_ = v_a_697_;
v___y_649_ = v___x_700_;
v_a_650_ = v_a_746_;
goto v___jp_647_;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_env_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = lean_io_get_num_heartbeats();
v___x_748_ = lean_st_ref_get(v_a_568_);
v_env_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_env_749_);
lean_dec(v___x_748_);
v___x_750_ = lean_elab_environment_to_kernel_env(v_env_749_);
v___x_751_ = lean_mk_cases_on(v___x_750_, v_declName_564_);
lean_dec(v_declName_564_);
v___x_752_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_751_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; uint8_t v___x_754_; lean_object* v___x_755_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = 0;
v___x_755_ = l_Lean_addDecl(v_a_753_, v___x_754_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_env_758_; lean_object* v_nextMacroScope_759_; lean_object* v_ngen_760_; lean_object* v_auxDeclNGen_761_; lean_object* v_traceState_762_; lean_object* v_messages_763_; lean_object* v_infoState_764_; lean_object* v_snapshotTasks_765_; lean_object* v_newDecls_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v___x_755_);
lean_inc(v_name_573_);
v___x_756_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_573_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec_ref(v___x_756_);
v___x_757_ = lean_st_ref_take(v_a_568_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
v_nextMacroScope_759_ = lean_ctor_get(v___x_757_, 1);
v_ngen_760_ = lean_ctor_get(v___x_757_, 2);
v_auxDeclNGen_761_ = lean_ctor_get(v___x_757_, 3);
v_traceState_762_ = lean_ctor_get(v___x_757_, 4);
v_messages_763_ = lean_ctor_get(v___x_757_, 6);
v_infoState_764_ = lean_ctor_get(v___x_757_, 7);
v_snapshotTasks_765_ = lean_ctor_get(v___x_757_, 8);
v_newDecls_766_ = lean_ctor_get(v___x_757_, 9);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_757_, 5);
lean_dec(v_unused_793_);
v___x_768_ = v___x_757_;
v_isShared_769_ = v_isSharedCheck_792_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_newDecls_766_);
lean_inc(v_snapshotTasks_765_);
lean_inc(v_infoState_764_);
lean_inc(v_messages_763_);
lean_inc(v_traceState_762_);
lean_inc(v_auxDeclNGen_761_);
lean_inc(v_ngen_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_env_758_);
lean_dec(v___x_757_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_792_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_inc(v_name_573_);
v___x_770_ = l_Lean_markAuxRecursor(v_env_758_, v_name_573_);
v___x_771_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 5, v___x_771_);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_ngen_760_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_auxDeclNGen_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_traceState_762_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_messages_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_infoState_764_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_snapshotTasks_765_);
lean_ctor_set(v_reuseFailAlloc_791_, 9, v_newDecls_766_);
v___x_773_ = v_reuseFailAlloc_791_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_mctx_776_; lean_object* v_zetaDeltaFVarIds_777_; lean_object* v_postponed_778_; lean_object* v_diag_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_789_; 
v___x_774_ = lean_st_ref_set(v_a_568_, v___x_773_);
v___x_775_ = lean_st_ref_take(v_a_566_);
v_mctx_776_ = lean_ctor_get(v___x_775_, 0);
v_zetaDeltaFVarIds_777_ = lean_ctor_get(v___x_775_, 2);
v_postponed_778_ = lean_ctor_get(v___x_775_, 3);
v_diag_779_ = lean_ctor_get(v___x_775_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_775_, 1);
lean_dec(v_unused_790_);
v___x_781_ = v___x_775_;
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_diag_779_);
lean_inc(v_postponed_778_);
lean_inc(v_zetaDeltaFVarIds_777_);
lean_inc(v_mctx_776_);
lean_dec(v___x_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_mctx_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_zetaDeltaFVarIds_777_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_postponed_778_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_diag_779_);
v___x_785_ = v_reuseFailAlloc_788_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_st_ref_set(v_a_566_, v___x_785_);
v___x_787_ = l_Lean_enableRealizationsForConst(v_name_573_, v_a_567_, v_a_568_);
v___y_683_ = v_a_697_;
v___y_684_ = v___x_747_;
v___y_685_ = v___x_787_;
goto v___jp_682_;
}
}
}
}
}
else
{
lean_dec(v_name_573_);
v___y_683_ = v_a_697_;
v___y_684_ = v___x_747_;
v___y_685_ = v___x_755_;
goto v___jp_682_;
}
}
else
{
lean_object* v_a_794_; 
lean_dec(v_name_573_);
v_a_794_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_752_);
v___y_678_ = v_a_697_;
v___y_679_ = v___x_747_;
v_a_680_ = v_a_794_;
goto v___jp_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_mkCasesOn(v_declName_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object* v_00_u03b1_857_, lean_object* v_x_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_00_u03b1_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(v_00_u03b1_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_declName_873_, uint8_t v_s_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_873_, v_s_874_, v___y_876_, v___y_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_declName_881_, lean_object* v_s_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_s_boxed_888_; lean_object* v_res_889_; 
v_s_boxed_888_ = lean_unbox(v_s_882_);
v_res_889_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(v_declName_881_, v_s_boxed_888_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object* v_00_u03b1_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___redArg(v_x_891_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object* v_00_u03b1_898_, lean_object* v_x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_00_u03b1_898_, v_x_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(v_00_u03b1_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_920_, lean_object* v_ex_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_928_, lean_object* v_ex_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(v_00_u03b1_928_, v_ex_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_936_, lean_object* v_msg_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v_msg_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_944_, lean_object* v_msg_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(v_00_u03b1_944_, v_msg_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_1013_ = 0;
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_1015_ = l_Lean_registerTraceClass(v___x_1012_, v___x_1013_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_1017_;
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

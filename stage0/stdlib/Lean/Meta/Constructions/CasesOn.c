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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_69_, 1);
if (lean_obj_tag(v_val_71_) == 1)
{
uint8_t v_v_72_; 
v_v_72_ = lean_ctor_get_uint8(v_val_71_, 0);
lean_dec_ref_known(v_val_71_, 0);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10(v_msgData_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
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
v___x_124_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
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
lean_dec_ref_known(v_x_179_, 1);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object* v_e_202_){
_start:
{
if (lean_obj_tag(v_e_202_) == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 2;
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object* v_e_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_e_205_);
lean_dec_ref(v_e_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v_x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v_x_208_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v_x_208_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 1);
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v_x_208_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v_x_208_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v_x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 0);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg___boxed(lean_object* v_x_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_x_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9(size_t v_sz_229_, size_t v_i_230_, lean_object* v_bs_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_lt(v_i_230_, v_sz_229_);
if (v___x_232_ == 0)
{
return v_bs_231_;
}
else
{
lean_object* v_v_233_; lean_object* v_msg_234_; lean_object* v___x_235_; lean_object* v_bs_x27_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; 
v_v_233_ = lean_array_uget_borrowed(v_bs_231_, v_i_230_);
v_msg_234_ = lean_ctor_get(v_v_233_, 1);
lean_inc_ref(v_msg_234_);
v___x_235_ = lean_unsigned_to_nat(0u);
v_bs_x27_236_ = lean_array_uset(v_bs_231_, v_i_230_, v___x_235_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_230_, v___x_237_);
v___x_239_ = lean_array_uset(v_bs_x27_236_, v_i_230_, v_msg_234_);
v_i_230_ = v___x_238_;
v_bs_231_ = v___x_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_bs_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9(v_sz_boxed_244_, v_i_boxed_245_, v_bs_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object* v_oldTraces_247_, lean_object* v_data_248_, lean_object* v_ref_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_fileName_256_; lean_object* v_fileMap_257_; lean_object* v_options_258_; lean_object* v_currRecDepth_259_; lean_object* v_maxRecDepth_260_; lean_object* v_ref_261_; lean_object* v_currNamespace_262_; lean_object* v_openDecls_263_; lean_object* v_initHeartbeats_264_; lean_object* v_maxHeartbeats_265_; lean_object* v_quotContext_266_; lean_object* v_currMacroScope_267_; uint8_t v_diag_268_; lean_object* v_cancelTk_x3f_269_; uint8_t v_suppressElabErrors_270_; lean_object* v_inheritedTraceOptions_271_; lean_object* v___x_272_; lean_object* v_traceState_273_; lean_object* v_traces_274_; lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v_msg_281_; lean_object* v___x_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_320_; 
v_fileName_256_ = lean_ctor_get(v___y_253_, 0);
v_fileMap_257_ = lean_ctor_get(v___y_253_, 1);
v_options_258_ = lean_ctor_get(v___y_253_, 2);
v_currRecDepth_259_ = lean_ctor_get(v___y_253_, 3);
v_maxRecDepth_260_ = lean_ctor_get(v___y_253_, 4);
v_ref_261_ = lean_ctor_get(v___y_253_, 5);
v_currNamespace_262_ = lean_ctor_get(v___y_253_, 6);
v_openDecls_263_ = lean_ctor_get(v___y_253_, 7);
v_initHeartbeats_264_ = lean_ctor_get(v___y_253_, 8);
v_maxHeartbeats_265_ = lean_ctor_get(v___y_253_, 9);
v_quotContext_266_ = lean_ctor_get(v___y_253_, 10);
v_currMacroScope_267_ = lean_ctor_get(v___y_253_, 11);
v_diag_268_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*14);
v_cancelTk_x3f_269_ = lean_ctor_get(v___y_253_, 12);
v_suppressElabErrors_270_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_271_ = lean_ctor_get(v___y_253_, 13);
v___x_272_ = lean_st_ref_get(v___y_254_);
v_traceState_273_ = lean_ctor_get(v___x_272_, 4);
lean_inc_ref(v_traceState_273_);
lean_dec(v___x_272_);
v_traces_274_ = lean_ctor_get(v_traceState_273_, 0);
lean_inc_ref(v_traces_274_);
lean_dec_ref(v_traceState_273_);
v_ref_275_ = l_Lean_replaceRef(v_ref_249_, v_ref_261_);
lean_inc_ref(v_inheritedTraceOptions_271_);
lean_inc(v_cancelTk_x3f_269_);
lean_inc(v_currMacroScope_267_);
lean_inc(v_quotContext_266_);
lean_inc(v_maxHeartbeats_265_);
lean_inc(v_initHeartbeats_264_);
lean_inc(v_openDecls_263_);
lean_inc(v_currNamespace_262_);
lean_inc(v_maxRecDepth_260_);
lean_inc(v_currRecDepth_259_);
lean_inc_ref(v_options_258_);
lean_inc_ref(v_fileMap_257_);
lean_inc_ref(v_fileName_256_);
v___x_276_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_276_, 0, v_fileName_256_);
lean_ctor_set(v___x_276_, 1, v_fileMap_257_);
lean_ctor_set(v___x_276_, 2, v_options_258_);
lean_ctor_set(v___x_276_, 3, v_currRecDepth_259_);
lean_ctor_set(v___x_276_, 4, v_maxRecDepth_260_);
lean_ctor_set(v___x_276_, 5, v_ref_275_);
lean_ctor_set(v___x_276_, 6, v_currNamespace_262_);
lean_ctor_set(v___x_276_, 7, v_openDecls_263_);
lean_ctor_set(v___x_276_, 8, v_initHeartbeats_264_);
lean_ctor_set(v___x_276_, 9, v_maxHeartbeats_265_);
lean_ctor_set(v___x_276_, 10, v_quotContext_266_);
lean_ctor_set(v___x_276_, 11, v_currMacroScope_267_);
lean_ctor_set(v___x_276_, 12, v_cancelTk_x3f_269_);
lean_ctor_set(v___x_276_, 13, v_inheritedTraceOptions_271_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*14, v_diag_268_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*14 + 1, v_suppressElabErrors_270_);
v___x_277_ = l_Lean_PersistentArray_toArray___redArg(v_traces_274_);
lean_dec_ref(v_traces_274_);
v_sz_278_ = lean_array_size(v___x_277_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__9(v_sz_278_, v___x_279_, v___x_277_);
v_msg_281_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_281_, 0, v_data_248_);
lean_ctor_set(v_msg_281_, 1, v_msg_250_);
lean_ctor_set(v_msg_281_, 2, v___x_280_);
v___x_282_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__10(v_msg_281_, v___y_251_, v___y_252_, v___x_276_, v___y_254_);
lean_dec_ref_known(v___x_276_, 14);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_320_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_320_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v_traceState_288_; lean_object* v_env_289_; lean_object* v_nextMacroScope_290_; lean_object* v_ngen_291_; lean_object* v_auxDeclNGen_292_; lean_object* v_cache_293_; lean_object* v_messages_294_; lean_object* v_infoState_295_; lean_object* v_snapshotTasks_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_319_; 
v___x_287_ = lean_st_ref_take(v___y_254_);
v_traceState_288_ = lean_ctor_get(v___x_287_, 4);
v_env_289_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_290_ = lean_ctor_get(v___x_287_, 1);
v_ngen_291_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_292_ = lean_ctor_get(v___x_287_, 3);
v_cache_293_ = lean_ctor_get(v___x_287_, 5);
v_messages_294_ = lean_ctor_get(v___x_287_, 6);
v_infoState_295_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_296_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_319_ == 0)
{
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snapshotTasks_296_);
lean_inc(v_infoState_295_);
lean_inc(v_messages_294_);
lean_inc(v_cache_293_);
lean_inc(v_traceState_288_);
lean_inc(v_auxDeclNGen_292_);
lean_inc(v_ngen_291_);
lean_inc(v_nextMacroScope_290_);
lean_inc(v_env_289_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint64_t v_tid_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_317_; 
v_tid_300_ = lean_ctor_get_uint64(v_traceState_288_, sizeof(void*)*1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_traceState_288_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_traceState_288_, 0);
lean_dec(v_unused_318_);
v___x_302_ = v_traceState_288_;
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_traceState_288_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_317_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_ref_249_);
lean_ctor_set(v___x_304_, 1, v_a_283_);
v___x_305_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_247_, v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_305_);
lean_ctor_set_uint64(v_reuseFailAlloc_316_, sizeof(void*)*1, v_tid_300_);
v___x_307_ = v_reuseFailAlloc_316_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v___x_307_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_env_289_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_nextMacroScope_290_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_ngen_291_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_auxDeclNGen_292_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v_cache_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_messages_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 7, v_infoState_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 8, v_snapshotTasks_296_);
v___x_309_ = v_reuseFailAlloc_315_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = lean_st_ref_set(v___y_254_, v___x_309_);
v___x_311_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_311_);
v___x_313_ = v___x_285_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object* v_oldTraces_321_, lean_object* v_data_322_, lean_object* v_ref_323_, lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_oldTraces_321_, v_data_322_, v_ref_323_, v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object* v_opts_331_, lean_object* v_opt_332_){
_start:
{
lean_object* v_name_333_; lean_object* v_defValue_334_; lean_object* v_map_335_; lean_object* v___x_336_; 
v_name_333_ = lean_ctor_get(v_opt_332_, 0);
v_defValue_334_ = lean_ctor_get(v_opt_332_, 1);
v_map_335_ = lean_ctor_get(v_opts_331_, 0);
v___x_336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_335_, v_name_333_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_inc(v_defValue_334_);
return v_defValue_334_;
}
else
{
lean_object* v_val_337_; 
v_val_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v___x_336_, 1);
if (lean_obj_tag(v_val_337_) == 3)
{
lean_object* v_v_338_; 
v_v_338_ = lean_ctor_get(v_val_337_, 0);
lean_inc(v_v_338_);
lean_dec_ref_known(v_val_337_, 1);
return v_v_338_;
}
else
{
lean_dec(v_val_337_);
lean_inc(v_defValue_334_);
return v_defValue_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object* v_opts_339_, lean_object* v_opt_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_339_, v_opt_340_);
lean_dec_ref(v_opt_340_);
lean_dec_ref(v_opts_339_);
return v_res_341_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0(void){
_start:
{
lean_object* v___x_342_; double v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_float_of_nat(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1));
v___x_346_ = l_Lean_stringToMessageData(v___x_345_);
return v___x_346_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3(void){
_start:
{
lean_object* v___x_347_; double v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1000u);
v___x_348_ = lean_float_of_nat(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object* v_cls_349_, uint8_t v_collapsed_350_, lean_object* v_tag_351_, lean_object* v_opts_352_, uint8_t v_clsEnabled_353_, lean_object* v_oldTraces_354_, lean_object* v_msg_355_, lean_object* v_resStartStop_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v_data_367_; lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___y_375_; lean_object* v_a_376_; uint8_t v___y_391_; double v___y_422_; 
v_fst_362_ = lean_ctor_get(v_resStartStop_356_, 0);
lean_inc(v_fst_362_);
v_snd_363_ = lean_ctor_get(v_resStartStop_356_, 1);
lean_inc(v_snd_363_);
lean_dec_ref(v_resStartStop_356_);
v_fst_370_ = lean_ctor_get(v_snd_363_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v_snd_363_, 1);
lean_inc(v_snd_371_);
lean_dec(v_snd_363_);
v___x_372_ = l_Lean_trace_profiler;
v___x_373_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_352_, v___x_372_);
if (v___x_373_ == 0)
{
v___y_391_ = v___x_373_;
goto v___jp_390_;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_trace_profiler_useHeartbeats;
v___x_428_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_352_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; double v___x_431_; double v___x_432_; double v___x_433_; 
v___x_429_ = l_Lean_trace_profiler_threshold;
v___x_430_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_352_, v___x_429_);
v___x_431_ = lean_float_of_nat(v___x_430_);
v___x_432_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3);
v___x_433_ = lean_float_div(v___x_431_, v___x_432_);
v___y_422_ = v___x_433_;
goto v___jp_421_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; double v___x_436_; 
v___x_434_ = l_Lean_trace_profiler_threshold;
v___x_435_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_352_, v___x_434_);
v___x_436_ = lean_float_of_nat(v___x_435_);
v___y_422_ = v___x_436_;
goto v___jp_421_;
}
}
v___jp_364_:
{
lean_object* v___x_368_; 
lean_inc(v___y_366_);
v___x_368_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_oldTraces_354_, v_data_367_, v___y_366_, v___y_365_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_369_; 
lean_dec_ref_known(v___x_368_, 1);
v___x_369_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_fst_362_);
return v___x_369_;
}
else
{
lean_dec(v_fst_362_);
return v___x_368_;
}
}
v___jp_374_:
{
uint8_t v_result_377_; lean_object* v___x_378_; lean_object* v___x_379_; double v___x_380_; lean_object* v_data_381_; 
v_result_377_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_fst_362_);
v___x_378_ = lean_box(v_result_377_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0);
lean_inc_ref(v_tag_351_);
lean_inc_ref(v___x_379_);
lean_inc(v_cls_349_);
v_data_381_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_381_, 0, v_cls_349_);
lean_ctor_set(v_data_381_, 1, v___x_379_);
lean_ctor_set(v_data_381_, 2, v_tag_351_);
lean_ctor_set_float(v_data_381_, sizeof(void*)*3, v___x_380_);
lean_ctor_set_float(v_data_381_, sizeof(void*)*3 + 8, v___x_380_);
lean_ctor_set_uint8(v_data_381_, sizeof(void*)*3 + 16, v_collapsed_350_);
if (v___x_373_ == 0)
{
lean_dec_ref_known(v___x_379_, 1);
lean_dec(v_snd_371_);
lean_dec(v_fst_370_);
lean_dec_ref(v_tag_351_);
lean_dec(v_cls_349_);
v___y_365_ = v_a_376_;
v___y_366_ = v___y_375_;
v_data_367_ = v_data_381_;
goto v___jp_364_;
}
else
{
lean_object* v_data_382_; double v___x_383_; double v___x_384_; 
lean_dec_ref_known(v_data_381_, 3);
v_data_382_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_382_, 0, v_cls_349_);
lean_ctor_set(v_data_382_, 1, v___x_379_);
lean_ctor_set(v_data_382_, 2, v_tag_351_);
v___x_383_ = lean_unbox_float(v_fst_370_);
lean_dec(v_fst_370_);
lean_ctor_set_float(v_data_382_, sizeof(void*)*3, v___x_383_);
v___x_384_ = lean_unbox_float(v_snd_371_);
lean_dec(v_snd_371_);
lean_ctor_set_float(v_data_382_, sizeof(void*)*3 + 8, v___x_384_);
lean_ctor_set_uint8(v_data_382_, sizeof(void*)*3 + 16, v_collapsed_350_);
v___y_365_ = v_a_376_;
v___y_366_ = v___y_375_;
v_data_367_ = v_data_382_;
goto v___jp_364_;
}
}
v___jp_385_:
{
lean_object* v_ref_386_; lean_object* v___x_387_; 
v_ref_386_ = lean_ctor_get(v___y_359_, 5);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v_fst_362_);
v___x_387_ = lean_apply_6(v_msg_355_, v_fst_362_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___y_375_ = v_ref_386_;
v_a_376_ = v_a_388_;
goto v___jp_374_;
}
else
{
lean_object* v___x_389_; 
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2);
v___y_375_ = v_ref_386_;
v_a_376_ = v___x_389_;
goto v___jp_374_;
}
}
v___jp_390_:
{
if (v_clsEnabled_353_ == 0)
{
if (v___y_391_ == 0)
{
lean_object* v___x_392_; lean_object* v_traceState_393_; lean_object* v_env_394_; lean_object* v_nextMacroScope_395_; lean_object* v_ngen_396_; lean_object* v_auxDeclNGen_397_; lean_object* v_cache_398_; lean_object* v_messages_399_; lean_object* v_infoState_400_; lean_object* v_snapshotTasks_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_snd_371_);
lean_dec(v_fst_370_);
lean_dec_ref(v_msg_355_);
lean_dec_ref(v_tag_351_);
lean_dec(v_cls_349_);
v___x_392_ = lean_st_ref_take(v___y_360_);
v_traceState_393_ = lean_ctor_get(v___x_392_, 4);
v_env_394_ = lean_ctor_get(v___x_392_, 0);
v_nextMacroScope_395_ = lean_ctor_get(v___x_392_, 1);
v_ngen_396_ = lean_ctor_get(v___x_392_, 2);
v_auxDeclNGen_397_ = lean_ctor_get(v___x_392_, 3);
v_cache_398_ = lean_ctor_get(v___x_392_, 5);
v_messages_399_ = lean_ctor_get(v___x_392_, 6);
v_infoState_400_ = lean_ctor_get(v___x_392_, 7);
v_snapshotTasks_401_ = lean_ctor_get(v___x_392_, 8);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_420_ == 0)
{
v___x_403_ = v___x_392_;
v_isShared_404_ = v_isSharedCheck_420_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snapshotTasks_401_);
lean_inc(v_infoState_400_);
lean_inc(v_messages_399_);
lean_inc(v_cache_398_);
lean_inc(v_traceState_393_);
lean_inc(v_auxDeclNGen_397_);
lean_inc(v_ngen_396_);
lean_inc(v_nextMacroScope_395_);
lean_inc(v_env_394_);
lean_dec(v___x_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_420_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint64_t v_tid_405_; lean_object* v_traces_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_419_; 
v_tid_405_ = lean_ctor_get_uint64(v_traceState_393_, sizeof(void*)*1);
v_traces_406_ = lean_ctor_get(v_traceState_393_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_traceState_393_);
if (v_isSharedCheck_419_ == 0)
{
v___x_408_ = v_traceState_393_;
v_isShared_409_ = v_isSharedCheck_419_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_traces_406_);
lean_dec(v_traceState_393_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_419_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_354_, v_traces_406_);
lean_dec_ref(v_traces_406_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_410_);
lean_ctor_set_uint64(v_reuseFailAlloc_418_, sizeof(void*)*1, v_tid_405_);
v___x_412_ = v_reuseFailAlloc_418_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v___x_412_);
v___x_414_ = v___x_403_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_env_394_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_nextMacroScope_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_ngen_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_auxDeclNGen_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_cache_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v_messages_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_infoState_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_snapshotTasks_401_);
v___x_414_ = v_reuseFailAlloc_417_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_st_ref_set(v___y_360_, v___x_414_);
v___x_416_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_fst_362_);
return v___x_416_;
}
}
}
}
}
else
{
goto v___jp_385_;
}
}
else
{
goto v___jp_385_;
}
}
v___jp_421_:
{
double v___x_423_; double v___x_424_; double v___x_425_; uint8_t v___x_426_; 
v___x_423_ = lean_unbox_float(v_snd_371_);
v___x_424_ = lean_unbox_float(v_fst_370_);
v___x_425_ = lean_float_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_float_decLt(v___y_422_, v___x_425_);
v___y_391_ = v___x_426_;
goto v___jp_390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_cls_437_, lean_object* v_collapsed_438_, lean_object* v_tag_439_, lean_object* v_opts_440_, lean_object* v_clsEnabled_441_, lean_object* v_oldTraces_442_, lean_object* v_msg_443_, lean_object* v_resStartStop_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v_collapsed_boxed_450_; uint8_t v_clsEnabled_boxed_451_; lean_object* v_res_452_; 
v_collapsed_boxed_450_ = lean_unbox(v_collapsed_438_);
v_clsEnabled_boxed_451_ = lean_unbox(v_clsEnabled_441_);
v_res_452_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v_cls_437_, v_collapsed_boxed_450_, v_tag_439_, v_opts_440_, v_clsEnabled_boxed_451_, v_oldTraces_442_, v_msg_443_, v_resStartStop_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_opts_440_);
return v_res_452_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_453_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__1);
v___x_459_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
lean_ctor_set(v___x_459_, 3, v___x_458_);
lean_ctor_set(v___x_459_, 4, v___x_458_);
lean_ctor_set(v___x_459_, 5, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object* v_declName_460_, uint8_t v_s_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; lean_object* v_env_466_; lean_object* v_nextMacroScope_467_; lean_object* v_ngen_468_; lean_object* v_auxDeclNGen_469_; lean_object* v_traceState_470_; lean_object* v_messages_471_; lean_object* v_infoState_472_; lean_object* v_snapshotTasks_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_502_; 
v___x_465_ = lean_st_ref_take(v___y_463_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
v_nextMacroScope_467_ = lean_ctor_get(v___x_465_, 1);
v_ngen_468_ = lean_ctor_get(v___x_465_, 2);
v_auxDeclNGen_469_ = lean_ctor_get(v___x_465_, 3);
v_traceState_470_ = lean_ctor_get(v___x_465_, 4);
v_messages_471_ = lean_ctor_get(v___x_465_, 6);
v_infoState_472_ = lean_ctor_get(v___x_465_, 7);
v_snapshotTasks_473_ = lean_ctor_get(v___x_465_, 8);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_465_, 5);
lean_dec(v_unused_503_);
v___x_475_ = v___x_465_;
v_isShared_476_ = v_isSharedCheck_502_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snapshotTasks_473_);
lean_inc(v_infoState_472_);
lean_inc(v_messages_471_);
lean_inc(v_traceState_470_);
lean_inc(v_auxDeclNGen_469_);
lean_inc(v_ngen_468_);
lean_inc(v_nextMacroScope_467_);
lean_inc(v_env_466_);
lean_dec(v___x_465_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_502_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_477_ = 0;
v___x_478_ = lean_box(0);
v___x_479_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_466_, v_declName_460_, v_s_461_, v___x_477_, v___x_478_);
v___x_480_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 5, v___x_480_);
lean_ctor_set(v___x_475_, 0, v___x_479_);
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_nextMacroScope_467_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_ngen_468_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_auxDeclNGen_469_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_traceState_470_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_messages_471_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v_infoState_472_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_snapshotTasks_473_);
v___x_482_ = v_reuseFailAlloc_501_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_mctx_485_; lean_object* v_zetaDeltaFVarIds_486_; lean_object* v_postponed_487_; lean_object* v_diag_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_499_; 
v___x_483_ = lean_st_ref_set(v___y_463_, v___x_482_);
v___x_484_ = lean_st_ref_take(v___y_462_);
v_mctx_485_ = lean_ctor_get(v___x_484_, 0);
v_zetaDeltaFVarIds_486_ = lean_ctor_get(v___x_484_, 2);
v_postponed_487_ = lean_ctor_get(v___x_484_, 3);
v_diag_488_ = lean_ctor_get(v___x_484_, 4);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_484_, 1);
lean_dec(v_unused_500_);
v___x_490_ = v___x_484_;
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_diag_488_);
lean_inc(v_postponed_487_);
lean_inc(v_zetaDeltaFVarIds_486_);
lean_inc(v_mctx_485_);
lean_dec(v___x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_mctx_485_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_zetaDeltaFVarIds_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_postponed_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_diag_488_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_st_ref_set(v___y_462_, v___x_494_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_declName_504_, lean_object* v_s_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_s_boxed_509_; lean_object* v_res_510_; 
v_s_boxed_509_ = lean_unbox(v_s_505_);
v_res_510_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_504_, v_s_boxed_509_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec(v___y_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(lean_object* v_declName_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; lean_object* v___x_518_; 
v___x_517_ = 0;
v___x_518_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_511_, v___x_517_, v___y_513_, v___y_515_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_declName_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_declName_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
static lean_object* _init_l_Lean_mkCasesOn___closed__6(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_536_ = ((lean_object*)(l_Lean_mkCasesOn___closed__5));
v___x_537_ = l_Lean_Name_append(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static double _init_l_Lean_mkCasesOn___closed__7(void){
_start:
{
lean_object* v___x_538_; double v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1000000000u);
v___x_539_ = lean_float_of_nat(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_options_546_; lean_object* v_inheritedTraceOptions_547_; uint8_t v_hasTrace_548_; lean_object* v_name_549_; 
v_options_546_ = lean_ctor_get(v_a_543_, 2);
v_inheritedTraceOptions_547_ = lean_ctor_get(v_a_543_, 13);
v_hasTrace_548_ = lean_ctor_get_uint8(v_options_546_, sizeof(void*)*1);
lean_inc(v_declName_540_);
v_name_549_ = l_Lean_mkCasesOnName(v_declName_540_);
if (v_hasTrace_548_ == 0)
{
lean_object* v___x_550_; lean_object* v_env_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_550_ = lean_st_ref_get(v_a_544_);
v_env_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_550_);
v___x_552_ = lean_elab_environment_to_kernel_env(v_env_551_);
v___x_553_ = lean_mk_cases_on(v___x_552_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_554_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_553_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = l_Lean_addDecl(v_a_555_, v_hasTrace_548_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_env_559_; lean_object* v_nextMacroScope_560_; lean_object* v_ngen_561_; lean_object* v_auxDeclNGen_562_; lean_object* v_traceState_563_; lean_object* v_messages_564_; lean_object* v_infoState_565_; lean_object* v_snapshotTasks_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref_known(v___x_556_, 1);
lean_inc(v_name_549_);
v___x_557_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_557_);
v___x_558_ = lean_st_ref_take(v_a_544_);
v_env_559_ = lean_ctor_get(v___x_558_, 0);
v_nextMacroScope_560_ = lean_ctor_get(v___x_558_, 1);
v_ngen_561_ = lean_ctor_get(v___x_558_, 2);
v_auxDeclNGen_562_ = lean_ctor_get(v___x_558_, 3);
v_traceState_563_ = lean_ctor_get(v___x_558_, 4);
v_messages_564_ = lean_ctor_get(v___x_558_, 6);
v_infoState_565_ = lean_ctor_get(v___x_558_, 7);
v_snapshotTasks_566_ = lean_ctor_get(v___x_558_, 8);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_558_, 5);
lean_dec(v_unused_593_);
v___x_568_ = v___x_558_;
v_isShared_569_ = v_isSharedCheck_592_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snapshotTasks_566_);
lean_inc(v_infoState_565_);
lean_inc(v_messages_564_);
lean_inc(v_traceState_563_);
lean_inc(v_auxDeclNGen_562_);
lean_inc(v_ngen_561_);
lean_inc(v_nextMacroScope_560_);
lean_inc(v_env_559_);
lean_dec(v___x_558_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_592_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_inc(v_name_549_);
v___x_570_ = l_Lean_markAuxRecursor(v_env_559_, v_name_549_);
v___x_571_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 5, v___x_571_);
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_573_ = v___x_568_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_nextMacroScope_560_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_ngen_561_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_auxDeclNGen_562_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_traceState_563_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_messages_564_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_infoState_565_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_snapshotTasks_566_);
v___x_573_ = v_reuseFailAlloc_591_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_mctx_576_; lean_object* v_zetaDeltaFVarIds_577_; lean_object* v_postponed_578_; lean_object* v_diag_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v___x_574_ = lean_st_ref_set(v_a_544_, v___x_573_);
v___x_575_ = lean_st_ref_take(v_a_542_);
v_mctx_576_ = lean_ctor_get(v___x_575_, 0);
v_zetaDeltaFVarIds_577_ = lean_ctor_get(v___x_575_, 2);
v_postponed_578_ = lean_ctor_get(v___x_575_, 3);
v_diag_579_ = lean_ctor_get(v___x_575_, 4);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_575_, 1);
lean_dec(v_unused_590_);
v___x_581_ = v___x_575_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_diag_579_);
lean_inc(v_postponed_578_);
lean_inc(v_zetaDeltaFVarIds_577_);
lean_inc(v_mctx_576_);
lean_dec(v___x_575_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_583_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_mctx_576_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_zetaDeltaFVarIds_577_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_postponed_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_diag_579_);
v___x_585_ = v_reuseFailAlloc_588_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_st_ref_set(v_a_542_, v___x_585_);
v___x_587_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
return v___x_587_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
return v___x_556_;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_name_549_);
v_a_594_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_554_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_554_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v_a_610_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_a_625_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v_a_643_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v_a_655_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; 
lean_inc(v_declName_540_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_602_, 0, v_declName_540_);
v___x_603_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_604_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_605_ = lean_obj_once(&l_Lean_mkCasesOn___closed__6, &l_Lean_mkCasesOn___closed__6_once, _init_l_Lean_mkCasesOn___closed__6);
v___x_606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_547_, v_options_546_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_trace_profiler;
v___x_769_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_546_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v_env_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v___f_602_);
v___x_770_ = lean_st_ref_get(v_a_544_);
v_env_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_ref(v_env_771_);
lean_dec(v___x_770_);
v___x_772_ = lean_elab_environment_to_kernel_env(v_env_771_);
v___x_773_ = lean_mk_cases_on(v___x_772_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_774_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_773_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = l_Lean_addDecl(v_a_775_, v___x_769_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_env_779_; lean_object* v_nextMacroScope_780_; lean_object* v_ngen_781_; lean_object* v_auxDeclNGen_782_; lean_object* v_traceState_783_; lean_object* v_messages_784_; lean_object* v_infoState_785_; lean_object* v_snapshotTasks_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref_known(v___x_776_, 1);
lean_inc(v_name_549_);
v___x_777_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_777_);
v___x_778_ = lean_st_ref_take(v_a_544_);
v_env_779_ = lean_ctor_get(v___x_778_, 0);
v_nextMacroScope_780_ = lean_ctor_get(v___x_778_, 1);
v_ngen_781_ = lean_ctor_get(v___x_778_, 2);
v_auxDeclNGen_782_ = lean_ctor_get(v___x_778_, 3);
v_traceState_783_ = lean_ctor_get(v___x_778_, 4);
v_messages_784_ = lean_ctor_get(v___x_778_, 6);
v_infoState_785_ = lean_ctor_get(v___x_778_, 7);
v_snapshotTasks_786_ = lean_ctor_get(v___x_778_, 8);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_778_, 5);
lean_dec(v_unused_813_);
v___x_788_ = v___x_778_;
v_isShared_789_ = v_isSharedCheck_812_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snapshotTasks_786_);
lean_inc(v_infoState_785_);
lean_inc(v_messages_784_);
lean_inc(v_traceState_783_);
lean_inc(v_auxDeclNGen_782_);
lean_inc(v_ngen_781_);
lean_inc(v_nextMacroScope_780_);
lean_inc(v_env_779_);
lean_dec(v___x_778_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_812_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc(v_name_549_);
v___x_790_ = l_Lean_markAuxRecursor(v_env_779_, v_name_549_);
v___x_791_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 5, v___x_791_);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_nextMacroScope_780_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_ngen_781_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_auxDeclNGen_782_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_traceState_783_);
lean_ctor_set(v_reuseFailAlloc_811_, 5, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_811_, 6, v_messages_784_);
lean_ctor_set(v_reuseFailAlloc_811_, 7, v_infoState_785_);
lean_ctor_set(v_reuseFailAlloc_811_, 8, v_snapshotTasks_786_);
v___x_793_ = v_reuseFailAlloc_811_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_mctx_796_; lean_object* v_zetaDeltaFVarIds_797_; lean_object* v_postponed_798_; lean_object* v_diag_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_809_; 
v___x_794_ = lean_st_ref_set(v_a_544_, v___x_793_);
v___x_795_ = lean_st_ref_take(v_a_542_);
v_mctx_796_ = lean_ctor_get(v___x_795_, 0);
v_zetaDeltaFVarIds_797_ = lean_ctor_get(v___x_795_, 2);
v_postponed_798_ = lean_ctor_get(v___x_795_, 3);
v_diag_799_ = lean_ctor_get(v___x_795_, 4);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_795_, 1);
lean_dec(v_unused_810_);
v___x_801_ = v___x_795_;
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_diag_799_);
lean_inc(v_postponed_798_);
lean_inc(v_zetaDeltaFVarIds_797_);
lean_inc(v_mctx_796_);
lean_dec(v___x_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_mctx_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_zetaDeltaFVarIds_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_postponed_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_diag_799_);
v___x_805_ = v_reuseFailAlloc_808_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_st_ref_set(v_a_542_, v___x_805_);
v___x_807_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
return v___x_807_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
return v___x_776_;
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_name_549_);
v_a_814_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_774_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_774_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
goto v___jp_670_;
}
}
else
{
goto v___jp_670_;
}
v___jp_607_:
{
lean_object* v___x_611_; double v___x_612_; double v___x_613_; double v___x_614_; double v___x_615_; double v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_611_ = lean_io_mono_nanos_now();
v___x_612_ = lean_float_of_nat(v___y_608_);
v___x_613_ = lean_float_once(&l_Lean_mkCasesOn___closed__7, &l_Lean_mkCasesOn___closed__7_once, _init_l_Lean_mkCasesOn___closed__7);
v___x_614_ = lean_float_div(v___x_612_, v___x_613_);
v___x_615_ = lean_float_of_nat(v___x_611_);
v___x_616_ = lean_float_div(v___x_615_, v___x_613_);
v___x_617_ = lean_box_float(v___x_614_);
v___x_618_ = lean_box_float(v___x_616_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_a_610_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_603_, v_hasTrace_548_, v___x_604_, v_options_546_, v___x_606_, v___y_609_, v___f_602_, v___x_620_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_621_;
}
v___jp_622_:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_a_625_);
v___y_608_ = v___y_623_;
v___y_609_ = v___y_624_;
v_a_610_ = v___x_626_;
goto v___jp_607_;
}
v___jp_627_:
{
if (lean_obj_tag(v___y_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_a_631_ = lean_ctor_get(v___y_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___y_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___y_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___y_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 1);
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_608_ = v___y_628_;
v___y_609_ = v___y_629_;
v_a_610_ = v___x_636_;
goto v___jp_607_;
}
}
}
else
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___y_630_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___y_630_, 1);
v___y_623_ = v___y_628_;
v___y_624_ = v___y_629_;
v_a_625_ = v_a_639_;
goto v___jp_622_;
}
}
v___jp_640_:
{
lean_object* v___x_644_; double v___x_645_; double v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_644_ = lean_io_get_num_heartbeats();
v___x_645_ = lean_float_of_nat(v___y_641_);
v___x_646_ = lean_float_of_nat(v___x_644_);
v___x_647_ = lean_box_float(v___x_645_);
v___x_648_ = lean_box_float(v___x_646_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_a_643_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_603_, v_hasTrace_548_, v___x_604_, v_options_546_, v___x_606_, v___y_642_, v___f_602_, v___x_650_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_651_;
}
v___jp_652_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_a_655_);
v___y_641_ = v___y_653_;
v___y_642_ = v___y_654_;
v_a_643_ = v___x_656_;
goto v___jp_640_;
}
v___jp_657_:
{
if (lean_obj_tag(v___y_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___y_660_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___y_660_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___y_660_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___y_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v___y_641_ = v___y_658_;
v___y_642_ = v___y_659_;
v_a_643_ = v___x_666_;
goto v___jp_640_;
}
}
}
else
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___y_660_, 1);
v___y_653_ = v___y_658_;
v___y_654_ = v___y_659_;
v_a_655_ = v_a_669_;
goto v___jp_652_;
}
}
v___jp_670_:
{
lean_object* v___x_671_; lean_object* v_a_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_671_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v_a_544_);
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref(v___x_671_);
v___x_673_ = l_Lean_trace_profiler_useHeartbeats;
v___x_674_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_546_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_env_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = lean_io_mono_nanos_now();
v___x_676_ = lean_st_ref_get(v_a_544_);
v_env_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_env_677_);
lean_dec(v___x_676_);
v___x_678_ = lean_elab_environment_to_kernel_env(v_env_677_);
v___x_679_ = lean_mk_cases_on(v___x_678_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_680_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_679_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = l_Lean_addDecl(v_a_681_, v___x_674_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_env_685_; lean_object* v_nextMacroScope_686_; lean_object* v_ngen_687_; lean_object* v_auxDeclNGen_688_; lean_object* v_traceState_689_; lean_object* v_messages_690_; lean_object* v_infoState_691_; lean_object* v_snapshotTasks_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref_known(v___x_682_, 1);
lean_inc(v_name_549_);
v___x_683_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_683_);
v___x_684_ = lean_st_ref_take(v_a_544_);
v_env_685_ = lean_ctor_get(v___x_684_, 0);
v_nextMacroScope_686_ = lean_ctor_get(v___x_684_, 1);
v_ngen_687_ = lean_ctor_get(v___x_684_, 2);
v_auxDeclNGen_688_ = lean_ctor_get(v___x_684_, 3);
v_traceState_689_ = lean_ctor_get(v___x_684_, 4);
v_messages_690_ = lean_ctor_get(v___x_684_, 6);
v_infoState_691_ = lean_ctor_get(v___x_684_, 7);
v_snapshotTasks_692_ = lean_ctor_get(v___x_684_, 8);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_684_, 5);
lean_dec(v_unused_719_);
v___x_694_ = v___x_684_;
v_isShared_695_ = v_isSharedCheck_718_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snapshotTasks_692_);
lean_inc(v_infoState_691_);
lean_inc(v_messages_690_);
lean_inc(v_traceState_689_);
lean_inc(v_auxDeclNGen_688_);
lean_inc(v_ngen_687_);
lean_inc(v_nextMacroScope_686_);
lean_inc(v_env_685_);
lean_dec(v___x_684_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_718_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_inc(v_name_549_);
v___x_696_ = l_Lean_markAuxRecursor(v_env_685_, v_name_549_);
v___x_697_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 5, v___x_697_);
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_nextMacroScope_686_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_ngen_687_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_auxDeclNGen_688_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_traceState_689_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_messages_690_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_infoState_691_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_snapshotTasks_692_);
v___x_699_ = v_reuseFailAlloc_717_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_mctx_702_; lean_object* v_zetaDeltaFVarIds_703_; lean_object* v_postponed_704_; lean_object* v_diag_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_715_; 
v___x_700_ = lean_st_ref_set(v_a_544_, v___x_699_);
v___x_701_ = lean_st_ref_take(v_a_542_);
v_mctx_702_ = lean_ctor_get(v___x_701_, 0);
v_zetaDeltaFVarIds_703_ = lean_ctor_get(v___x_701_, 2);
v_postponed_704_ = lean_ctor_get(v___x_701_, 3);
v_diag_705_ = lean_ctor_get(v___x_701_, 4);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_701_, 1);
lean_dec(v_unused_716_);
v___x_707_ = v___x_701_;
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_diag_705_);
lean_inc(v_postponed_704_);
lean_inc(v_zetaDeltaFVarIds_703_);
lean_inc(v_mctx_702_);
lean_dec(v___x_701_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_mctx_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_zetaDeltaFVarIds_703_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_postponed_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_diag_705_);
v___x_711_ = v_reuseFailAlloc_714_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_st_ref_set(v_a_542_, v___x_711_);
v___x_713_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
v___y_628_ = v___x_675_;
v___y_629_ = v_a_672_;
v___y_630_ = v___x_713_;
goto v___jp_627_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
v___y_628_ = v___x_675_;
v___y_629_ = v_a_672_;
v___y_630_ = v___x_682_;
goto v___jp_627_;
}
}
else
{
lean_object* v_a_720_; 
lean_dec(v_name_549_);
v_a_720_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_680_, 1);
v___y_623_ = v___x_675_;
v___y_624_ = v_a_672_;
v_a_625_ = v_a_720_;
goto v___jp_622_;
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_env_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = lean_io_get_num_heartbeats();
v___x_722_ = lean_st_ref_get(v_a_544_);
v_env_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_723_);
lean_dec(v___x_722_);
v___x_724_ = lean_elab_environment_to_kernel_env(v_env_723_);
v___x_725_ = lean_mk_cases_on(v___x_724_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_726_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v___x_725_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; uint8_t v___x_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = 0;
v___x_729_ = l_Lean_addDecl(v_a_727_, v___x_728_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_env_732_; lean_object* v_nextMacroScope_733_; lean_object* v_ngen_734_; lean_object* v_auxDeclNGen_735_; lean_object* v_traceState_736_; lean_object* v_messages_737_; lean_object* v_infoState_738_; lean_object* v_snapshotTasks_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref_known(v___x_729_, 1);
lean_inc(v_name_549_);
v___x_730_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_730_);
v___x_731_ = lean_st_ref_take(v_a_544_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
v_nextMacroScope_733_ = lean_ctor_get(v___x_731_, 1);
v_ngen_734_ = lean_ctor_get(v___x_731_, 2);
v_auxDeclNGen_735_ = lean_ctor_get(v___x_731_, 3);
v_traceState_736_ = lean_ctor_get(v___x_731_, 4);
v_messages_737_ = lean_ctor_get(v___x_731_, 6);
v_infoState_738_ = lean_ctor_get(v___x_731_, 7);
v_snapshotTasks_739_ = lean_ctor_get(v___x_731_, 8);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_731_, 5);
lean_dec(v_unused_766_);
v___x_741_ = v___x_731_;
v_isShared_742_ = v_isSharedCheck_765_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snapshotTasks_739_);
lean_inc(v_infoState_738_);
lean_inc(v_messages_737_);
lean_inc(v_traceState_736_);
lean_inc(v_auxDeclNGen_735_);
lean_inc(v_ngen_734_);
lean_inc(v_nextMacroScope_733_);
lean_inc(v_env_732_);
lean_dec(v___x_731_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_765_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_inc(v_name_549_);
v___x_743_ = l_Lean_markAuxRecursor(v_env_732_, v_name_549_);
v___x_744_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__2);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 5, v___x_744_);
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_nextMacroScope_733_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_ngen_734_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_auxDeclNGen_735_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_traceState_736_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_messages_737_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_infoState_738_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_snapshotTasks_739_);
v___x_746_ = v_reuseFailAlloc_764_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_mctx_749_; lean_object* v_zetaDeltaFVarIds_750_; lean_object* v_postponed_751_; lean_object* v_diag_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v___x_747_ = lean_st_ref_set(v_a_544_, v___x_746_);
v___x_748_ = lean_st_ref_take(v_a_542_);
v_mctx_749_ = lean_ctor_get(v___x_748_, 0);
v_zetaDeltaFVarIds_750_ = lean_ctor_get(v___x_748_, 2);
v_postponed_751_ = lean_ctor_get(v___x_748_, 3);
v_diag_752_ = lean_ctor_get(v___x_748_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_748_, 1);
lean_dec(v_unused_763_);
v___x_754_ = v___x_748_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_diag_752_);
lean_inc(v_postponed_751_);
lean_inc(v_zetaDeltaFVarIds_750_);
lean_inc(v_mctx_749_);
lean_dec(v___x_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___closed__3);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_mctx_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_zetaDeltaFVarIds_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_postponed_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_diag_752_);
v___x_758_ = v_reuseFailAlloc_761_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_st_ref_set(v_a_542_, v___x_758_);
v___x_760_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
v___y_658_ = v___x_721_;
v___y_659_ = v_a_672_;
v___y_660_ = v___x_760_;
goto v___jp_657_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
v___y_658_ = v___x_721_;
v___y_659_ = v_a_672_;
v___y_660_ = v___x_729_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_767_; 
lean_dec(v_name_549_);
v_a_767_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_726_, 1);
v___y_653_ = v___x_721_;
v___y_654_ = v_a_672_;
v_a_655_ = v_a_767_;
goto v___jp_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_mkCasesOn(v_declName_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(lean_object* v_00_u03b1_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___redArg(v_x_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_00_u03b1_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0(v_00_u03b1_837_, v_x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_declName_845_, uint8_t v_s_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_declName_845_, v_s_846_, v___y_848_, v___y_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_declName_853_, lean_object* v_s_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_s_boxed_860_; lean_object* v_res_861_; 
v_s_boxed_860_ = lean_unbox(v_s_854_);
v_res_861_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__1_spec__2(v_declName_853_, v_s_boxed_860_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object* v_00_u03b1_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_x_863_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object* v_00_u03b1_870_, lean_object* v_x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_00_u03b1_870_, v_x_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___redArg();
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__4(v_00_u03b1_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_892_, lean_object* v_ex_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_ex_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_900_, lean_object* v_ex_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0(v_00_u03b1_900_, v_ex_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_908_, lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___redArg(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_916_, lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__0_spec__0_spec__3(v_00_u03b1_916_, v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_984_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_985_ = 0;
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_987_ = l_Lean_registerTraceClass(v___x_984_, v___x_985_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_989_;
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

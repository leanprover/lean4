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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnImp___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_mkCasesOn___closed__5 = (const lean_object*)&l_Lean_mkCasesOn___closed__5_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_mkCasesOn___closed__6 = (const lean_object*)&l_Lean_mkCasesOn___closed__6_value;
static lean_once_cell_t l_Lean_mkCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = ((size_t)5ULL);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_unsigned_to_nat(32u);
v___x_12_ = lean_mk_empty_array_with_capacity(v___x_11_);
v___x_13_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__0);
v___x_14_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_10_);
lean_ctor_set(v___x_14_, 3, v___x_10_);
lean_ctor_set_usize(v___x_14_, 4, v___x_9_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg(lean_object* v___y_15_){
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
v___x_37_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg___boxed(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg(v___y_49_);
lean_dec(v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0(lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg(v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0(v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(lean_object* v_opts_64_, lean_object* v_opt_65_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_opts_74_, lean_object* v_opt_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(v_opts_74_, v_opt_75_);
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
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_95_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__0);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__1);
v___x_101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v___x_100_);
lean_ctor_set(v___x_101_, 4, v___x_100_);
lean_ctor_set(v___x_101_, 5, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg(lean_object* v_declName_102_, uint8_t v_s_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v_nextMacroScope_109_; lean_object* v_ngen_110_; lean_object* v_auxDeclNGen_111_; lean_object* v_traceState_112_; lean_object* v_messages_113_; lean_object* v_infoState_114_; lean_object* v_snapshotTasks_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_144_; 
v___x_107_ = lean_st_ref_take(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
v_nextMacroScope_109_ = lean_ctor_get(v___x_107_, 1);
v_ngen_110_ = lean_ctor_get(v___x_107_, 2);
v_auxDeclNGen_111_ = lean_ctor_get(v___x_107_, 3);
v_traceState_112_ = lean_ctor_get(v___x_107_, 4);
v_messages_113_ = lean_ctor_get(v___x_107_, 6);
v_infoState_114_ = lean_ctor_get(v___x_107_, 7);
v_snapshotTasks_115_ = lean_ctor_get(v___x_107_, 8);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_107_, 5);
lean_dec(v_unused_145_);
v___x_117_ = v___x_107_;
v_isShared_118_ = v_isSharedCheck_144_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_snapshotTasks_115_);
lean_inc(v_infoState_114_);
lean_inc(v_messages_113_);
lean_inc(v_traceState_112_);
lean_inc(v_auxDeclNGen_111_);
lean_inc(v_ngen_110_);
lean_inc(v_nextMacroScope_109_);
lean_inc(v_env_108_);
lean_dec(v___x_107_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_144_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_119_ = 0;
v___x_120_ = lean_box(0);
v___x_121_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_108_, v_declName_102_, v_s_103_, v___x_119_, v___x_120_);
v___x_122_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 5, v___x_122_);
lean_ctor_set(v___x_117_, 0, v___x_121_);
v___x_124_ = v___x_117_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_nextMacroScope_109_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_ngen_110_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_auxDeclNGen_111_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_traceState_112_);
lean_ctor_set(v_reuseFailAlloc_143_, 5, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 6, v_messages_113_);
lean_ctor_set(v_reuseFailAlloc_143_, 7, v_infoState_114_);
lean_ctor_set(v_reuseFailAlloc_143_, 8, v_snapshotTasks_115_);
v___x_124_ = v_reuseFailAlloc_143_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_mctx_127_; lean_object* v_zetaDeltaFVarIds_128_; lean_object* v_postponed_129_; lean_object* v_diag_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_141_; 
v___x_125_ = lean_st_ref_set(v___y_105_, v___x_124_);
v___x_126_ = lean_st_ref_take(v___y_104_);
v_mctx_127_ = lean_ctor_get(v___x_126_, 0);
v_zetaDeltaFVarIds_128_ = lean_ctor_get(v___x_126_, 2);
v_postponed_129_ = lean_ctor_get(v___x_126_, 3);
v_diag_130_ = lean_ctor_get(v___x_126_, 4);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v___x_126_, 1);
lean_dec(v_unused_142_);
v___x_132_ = v___x_126_;
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_diag_130_);
lean_inc(v_postponed_129_);
lean_inc(v_zetaDeltaFVarIds_128_);
lean_inc(v_mctx_127_);
lean_dec(v___x_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_mctx_127_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_zetaDeltaFVarIds_128_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_postponed_129_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_diag_130_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_st_ref_set(v___y_104_, v___x_136_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___boxed(lean_object* v_declName_146_, lean_object* v_s_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v_s_boxed_151_; lean_object* v_res_152_; 
v_s_boxed_151_ = lean_unbox(v_s_147_);
v_res_152_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg(v_declName_146_, v_s_boxed_151_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec(v___y_148_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(lean_object* v_declName_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v___x_159_; lean_object* v___x_160_; 
v___x_159_ = 0;
v___x_160_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg(v_declName_153_, v___x_159_, v___y_155_, v___y_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_declName_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(v_declName_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = l_Lean_interruptExceptionId;
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg(){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___closed__0);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_env_183_; lean_object* v___x_184_; lean_object* v_mctx_185_; lean_object* v_lctx_186_; lean_object* v_options_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_182_ = lean_st_ref_get(v___y_180_);
v_env_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_ref(v_env_183_);
lean_dec(v___x_182_);
v___x_184_ = lean_st_ref_get(v___y_178_);
v_mctx_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc_ref(v_mctx_185_);
lean_dec(v___x_184_);
v_lctx_186_ = lean_ctor_get(v___y_177_, 2);
v_options_187_ = lean_ctor_get(v___y_179_, 2);
lean_inc_ref(v_options_187_);
lean_inc_ref(v_lctx_186_);
v___x_188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_188_, 0, v_env_183_);
lean_ctor_set(v___x_188_, 1, v_mctx_185_);
lean_ctor_set(v___x_188_, 2, v_lctx_186_);
lean_ctor_set(v___x_188_, 3, v_options_187_);
v___x_189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_msgData_176_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4(v_msgData_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg(lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_ref_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_214_; 
v_ref_204_ = lean_ctor_get(v___y_201_, 5);
v___x_205_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4(v_msg_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_inc(v_ref_204_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_ref_204_);
lean_ctor_set(v___x_210_, 1, v_a_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 1);
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg(v_msg_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg(lean_object* v_ex_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; 
if (lean_obj_tag(v_ex_222_) == 16)
{
lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v___x_236_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg();
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
v___y_229_ = v___y_223_;
v___y_230_ = v___y_224_;
v___y_231_ = v___y_225_;
v___y_232_ = v___y_226_;
goto v___jp_228_;
}
v___jp_228_:
{
lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_options_233_ = lean_ctor_get(v___y_231_, 2);
lean_inc_ref(v_options_233_);
v___x_234_ = l_Lean_Kernel_Exception_toMessageData(v_ex_222_, v_options_233_);
v___x_235_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg(v___x_234_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg___boxed(lean_object* v_ex_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg(v_ex_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; 
v_a_258_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v_x_252_, 1);
v___x_259_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg(v_a_258_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_259_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_a_260_ = lean_ctor_get(v_x_252_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v_x_252_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v_x_252_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 0);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg___boxed(lean_object* v_x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v_x_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4(lean_object* v_e_275_){
_start:
{
if (lean_obj_tag(v_e_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 2;
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4___boxed(lean_object* v_e_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4(v_e_278_);
lean_dec_ref(v_e_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5(lean_object* v_opts_281_, lean_object* v_opt_282_){
_start:
{
lean_object* v_name_283_; lean_object* v_defValue_284_; lean_object* v_map_285_; lean_object* v___x_286_; 
v_name_283_ = lean_ctor_get(v_opt_282_, 0);
v_defValue_284_ = lean_ctor_get(v_opt_282_, 1);
v_map_285_ = lean_ctor_get(v_opts_281_, 0);
v___x_286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_285_, v_name_283_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_inc(v_defValue_284_);
return v_defValue_284_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_286_, 1);
if (lean_obj_tag(v_val_287_) == 3)
{
lean_object* v_v_288_; 
v_v_288_ = lean_ctor_get(v_val_287_, 0);
lean_inc(v_v_288_);
lean_dec_ref_known(v_val_287_, 1);
return v_v_288_;
}
else
{
lean_dec(v_val_287_);
lean_inc(v_defValue_284_);
return v_defValue_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5___boxed(lean_object* v_opts_289_, lean_object* v_opt_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5(v_opts_289_, v_opt_290_);
lean_dec_ref(v_opt_290_);
lean_dec_ref(v_opts_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3(size_t v_sz_292_, size_t v_i_293_, lean_object* v_bs_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_lt(v_i_293_, v_sz_292_);
if (v___x_295_ == 0)
{
return v_bs_294_;
}
else
{
lean_object* v_v_296_; lean_object* v_msg_297_; lean_object* v___x_298_; lean_object* v_bs_x27_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v_v_296_ = lean_array_uget_borrowed(v_bs_294_, v_i_293_);
v_msg_297_ = lean_ctor_get(v_v_296_, 1);
lean_inc_ref(v_msg_297_);
v___x_298_ = lean_unsigned_to_nat(0u);
v_bs_x27_299_ = lean_array_uset(v_bs_294_, v_i_293_, v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_add(v_i_293_, v___x_300_);
v___x_302_ = lean_array_uset(v_bs_x27_299_, v_i_293_, v_msg_297_);
v_i_293_ = v___x_301_;
v_bs_294_ = v___x_302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_304_, lean_object* v_i_305_, lean_object* v_bs_306_){
_start:
{
size_t v_sz_boxed_307_; size_t v_i_boxed_308_; lean_object* v_res_309_; 
v_sz_boxed_307_ = lean_unbox_usize(v_sz_304_);
lean_dec(v_sz_304_);
v_i_boxed_308_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3(v_sz_boxed_307_, v_i_boxed_308_, v_bs_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2(lean_object* v_oldTraces_310_, lean_object* v_data_311_, lean_object* v_ref_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_options_321_; lean_object* v_currRecDepth_322_; lean_object* v_maxRecDepth_323_; lean_object* v_ref_324_; lean_object* v_currNamespace_325_; lean_object* v_openDecls_326_; lean_object* v_initHeartbeats_327_; lean_object* v_maxHeartbeats_328_; lean_object* v_quotContext_329_; lean_object* v_currMacroScope_330_; uint8_t v_diag_331_; lean_object* v_cancelTk_x3f_332_; uint8_t v_suppressElabErrors_333_; lean_object* v_inheritedTraceOptions_334_; lean_object* v___x_335_; lean_object* v_traceState_336_; lean_object* v_traces_337_; lean_object* v_ref_338_; lean_object* v___x_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v_msg_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_383_; 
v_fileName_319_ = lean_ctor_get(v___y_316_, 0);
v_fileMap_320_ = lean_ctor_get(v___y_316_, 1);
v_options_321_ = lean_ctor_get(v___y_316_, 2);
v_currRecDepth_322_ = lean_ctor_get(v___y_316_, 3);
v_maxRecDepth_323_ = lean_ctor_get(v___y_316_, 4);
v_ref_324_ = lean_ctor_get(v___y_316_, 5);
v_currNamespace_325_ = lean_ctor_get(v___y_316_, 6);
v_openDecls_326_ = lean_ctor_get(v___y_316_, 7);
v_initHeartbeats_327_ = lean_ctor_get(v___y_316_, 8);
v_maxHeartbeats_328_ = lean_ctor_get(v___y_316_, 9);
v_quotContext_329_ = lean_ctor_get(v___y_316_, 10);
v_currMacroScope_330_ = lean_ctor_get(v___y_316_, 11);
v_diag_331_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*14);
v_cancelTk_x3f_332_ = lean_ctor_get(v___y_316_, 12);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_334_ = lean_ctor_get(v___y_316_, 13);
v___x_335_ = lean_st_ref_get(v___y_317_);
v_traceState_336_ = lean_ctor_get(v___x_335_, 4);
lean_inc_ref(v_traceState_336_);
lean_dec(v___x_335_);
v_traces_337_ = lean_ctor_get(v_traceState_336_, 0);
lean_inc_ref(v_traces_337_);
lean_dec_ref(v_traceState_336_);
v_ref_338_ = l_Lean_replaceRef(v_ref_312_, v_ref_324_);
lean_inc_ref(v_inheritedTraceOptions_334_);
lean_inc(v_cancelTk_x3f_332_);
lean_inc(v_currMacroScope_330_);
lean_inc(v_quotContext_329_);
lean_inc(v_maxHeartbeats_328_);
lean_inc(v_initHeartbeats_327_);
lean_inc(v_openDecls_326_);
lean_inc(v_currNamespace_325_);
lean_inc(v_maxRecDepth_323_);
lean_inc(v_currRecDepth_322_);
lean_inc_ref(v_options_321_);
lean_inc_ref(v_fileMap_320_);
lean_inc_ref(v_fileName_319_);
v___x_339_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_339_, 0, v_fileName_319_);
lean_ctor_set(v___x_339_, 1, v_fileMap_320_);
lean_ctor_set(v___x_339_, 2, v_options_321_);
lean_ctor_set(v___x_339_, 3, v_currRecDepth_322_);
lean_ctor_set(v___x_339_, 4, v_maxRecDepth_323_);
lean_ctor_set(v___x_339_, 5, v_ref_338_);
lean_ctor_set(v___x_339_, 6, v_currNamespace_325_);
lean_ctor_set(v___x_339_, 7, v_openDecls_326_);
lean_ctor_set(v___x_339_, 8, v_initHeartbeats_327_);
lean_ctor_set(v___x_339_, 9, v_maxHeartbeats_328_);
lean_ctor_set(v___x_339_, 10, v_quotContext_329_);
lean_ctor_set(v___x_339_, 11, v_currMacroScope_330_);
lean_ctor_set(v___x_339_, 12, v_cancelTk_x3f_332_);
lean_ctor_set(v___x_339_, 13, v_inheritedTraceOptions_334_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14, v_diag_331_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14 + 1, v_suppressElabErrors_333_);
v___x_340_ = l_Lean_PersistentArray_toArray___redArg(v_traces_337_);
lean_dec_ref(v_traces_337_);
v_sz_341_ = lean_array_size(v___x_340_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__3(v_sz_341_, v___x_342_, v___x_340_);
v_msg_344_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_344_, 0, v_data_311_);
lean_ctor_set(v_msg_344_, 1, v_msg_313_);
lean_ctor_set(v_msg_344_, 2, v___x_343_);
v___x_345_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2_spec__4(v_msg_344_, v___y_314_, v___y_315_, v___x_339_, v___y_317_);
lean_dec_ref_known(v___x_339_, 14);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_383_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_383_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_383_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v_traceState_351_; lean_object* v_env_352_; lean_object* v_nextMacroScope_353_; lean_object* v_ngen_354_; lean_object* v_auxDeclNGen_355_; lean_object* v_cache_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_382_; 
v___x_350_ = lean_st_ref_take(v___y_317_);
v_traceState_351_ = lean_ctor_get(v___x_350_, 4);
v_env_352_ = lean_ctor_get(v___x_350_, 0);
v_nextMacroScope_353_ = lean_ctor_get(v___x_350_, 1);
v_ngen_354_ = lean_ctor_get(v___x_350_, 2);
v_auxDeclNGen_355_ = lean_ctor_get(v___x_350_, 3);
v_cache_356_ = lean_ctor_get(v___x_350_, 5);
v_messages_357_ = lean_ctor_get(v___x_350_, 6);
v_infoState_358_ = lean_ctor_get(v___x_350_, 7);
v_snapshotTasks_359_ = lean_ctor_get(v___x_350_, 8);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_382_ == 0)
{
v___x_361_ = v___x_350_;
v_isShared_362_ = v_isSharedCheck_382_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_cache_356_);
lean_inc(v_traceState_351_);
lean_inc(v_auxDeclNGen_355_);
lean_inc(v_ngen_354_);
lean_inc(v_nextMacroScope_353_);
lean_inc(v_env_352_);
lean_dec(v___x_350_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_382_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
uint64_t v_tid_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_380_; 
v_tid_363_ = lean_ctor_get_uint64(v_traceState_351_, sizeof(void*)*1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_traceState_351_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_traceState_351_, 0);
lean_dec(v_unused_381_);
v___x_365_ = v_traceState_351_;
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_traceState_351_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_ref_312_);
lean_ctor_set(v___x_367_, 1, v_a_346_);
v___x_368_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_310_, v___x_367_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_368_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_368_);
lean_ctor_set_uint64(v_reuseFailAlloc_379_, sizeof(void*)*1, v_tid_363_);
v___x_370_ = v_reuseFailAlloc_379_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 4, v___x_370_);
v___x_372_ = v___x_361_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_env_352_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_nextMacroScope_353_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_ngen_354_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_auxDeclNGen_355_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_cache_356_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_snapshotTasks_359_);
v___x_372_ = v_reuseFailAlloc_378_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_st_ref_set(v___y_317_, v___x_372_);
v___x_374_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_374_);
v___x_376_ = v___x_348_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2___boxed(lean_object* v_oldTraces_384_, lean_object* v_data_385_, lean_object* v_ref_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2(v_oldTraces_384_, v_data_385_, v_ref_386_, v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v_x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v_x_394_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v_x_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v_x_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v_x_394_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v_x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg___boxed(lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(v_x_412_);
return v_res_414_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0(void){
_start:
{
lean_object* v___x_415_; double v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_float_of_nat(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__1));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3(void){
_start:
{
lean_object* v___x_420_; double v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(1000u);
v___x_421_ = lean_float_of_nat(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2(lean_object* v_cls_422_, uint8_t v_collapsed_423_, lean_object* v_tag_424_, lean_object* v_opts_425_, uint8_t v_clsEnabled_426_, lean_object* v_oldTraces_427_, lean_object* v_msg_428_, lean_object* v_resStartStop_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v_data_440_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___y_448_; lean_object* v_a_449_; uint8_t v___y_464_; double v___y_495_; 
v_fst_435_ = lean_ctor_get(v_resStartStop_429_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v_resStartStop_429_, 1);
lean_inc(v_snd_436_);
lean_dec_ref(v_resStartStop_429_);
v_fst_443_ = lean_ctor_get(v_snd_436_, 0);
lean_inc(v_fst_443_);
v_snd_444_ = lean_ctor_get(v_snd_436_, 1);
lean_inc(v_snd_444_);
lean_dec(v_snd_436_);
v___x_445_ = l_Lean_trace_profiler;
v___x_446_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(v_opts_425_, v___x_445_);
if (v___x_446_ == 0)
{
v___y_464_ = v___x_446_;
goto v___jp_463_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_501_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(v_opts_425_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; double v___x_505_; double v___x_506_; 
v___x_502_ = l_Lean_trace_profiler_threshold;
v___x_503_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5(v_opts_425_, v___x_502_);
v___x_504_ = lean_float_of_nat(v___x_503_);
v___x_505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__3);
v___x_506_ = lean_float_div(v___x_504_, v___x_505_);
v___y_495_ = v___x_506_;
goto v___jp_494_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; double v___x_509_; 
v___x_507_ = l_Lean_trace_profiler_threshold;
v___x_508_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__5(v_opts_425_, v___x_507_);
v___x_509_ = lean_float_of_nat(v___x_508_);
v___y_495_ = v___x_509_;
goto v___jp_494_;
}
}
v___jp_437_:
{
lean_object* v___x_441_; 
lean_inc(v___y_439_);
v___x_441_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__2(v_oldTraces_427_, v_data_440_, v___y_439_, v___y_438_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; 
lean_dec_ref_known(v___x_441_, 1);
v___x_442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(v_fst_435_);
return v___x_442_;
}
else
{
lean_dec(v_fst_435_);
return v___x_441_;
}
}
v___jp_447_:
{
uint8_t v_result_450_; lean_object* v___x_451_; lean_object* v___x_452_; double v___x_453_; lean_object* v_data_454_; 
v_result_450_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__4(v_fst_435_);
v___x_451_ = lean_box(v_result_450_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__0);
lean_inc_ref(v_tag_424_);
lean_inc_ref(v___x_452_);
lean_inc(v_cls_422_);
v_data_454_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_454_, 0, v_cls_422_);
lean_ctor_set(v_data_454_, 1, v___x_452_);
lean_ctor_set(v_data_454_, 2, v_tag_424_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3, v___x_453_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3 + 8, v___x_453_);
lean_ctor_set_uint8(v_data_454_, sizeof(void*)*3 + 16, v_collapsed_423_);
if (v___x_446_ == 0)
{
lean_dec_ref_known(v___x_452_, 1);
lean_dec(v_snd_444_);
lean_dec(v_fst_443_);
lean_dec_ref(v_tag_424_);
lean_dec(v_cls_422_);
v___y_438_ = v_a_449_;
v___y_439_ = v___y_448_;
v_data_440_ = v_data_454_;
goto v___jp_437_;
}
else
{
lean_object* v_data_455_; double v___x_456_; double v___x_457_; 
lean_dec_ref_known(v_data_454_, 3);
v_data_455_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_455_, 0, v_cls_422_);
lean_ctor_set(v_data_455_, 1, v___x_452_);
lean_ctor_set(v_data_455_, 2, v_tag_424_);
v___x_456_ = lean_unbox_float(v_fst_443_);
lean_dec(v_fst_443_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3, v___x_456_);
v___x_457_ = lean_unbox_float(v_snd_444_);
lean_dec(v_snd_444_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3 + 8, v___x_457_);
lean_ctor_set_uint8(v_data_455_, sizeof(void*)*3 + 16, v_collapsed_423_);
v___y_438_ = v_a_449_;
v___y_439_ = v___y_448_;
v_data_440_ = v_data_455_;
goto v___jp_437_;
}
}
v___jp_458_:
{
lean_object* v_ref_459_; lean_object* v___x_460_; 
v_ref_459_ = lean_ctor_get(v___y_432_, 5);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v_fst_435_);
v___x_460_ = lean_apply_6(v_msg_428_, v_fst_435_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___y_448_ = v_ref_459_;
v_a_449_ = v_a_461_;
goto v___jp_447_;
}
else
{
lean_object* v___x_462_; 
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___closed__2);
v___y_448_ = v_ref_459_;
v_a_449_ = v___x_462_;
goto v___jp_447_;
}
}
v___jp_463_:
{
if (v_clsEnabled_426_ == 0)
{
if (v___y_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_traceState_466_; lean_object* v_env_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_cache_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_snd_444_);
lean_dec(v_fst_443_);
lean_dec_ref(v_msg_428_);
lean_dec_ref(v_tag_424_);
lean_dec(v_cls_422_);
v___x_465_ = lean_st_ref_take(v___y_433_);
v_traceState_466_ = lean_ctor_get(v___x_465_, 4);
v_env_467_ = lean_ctor_get(v___x_465_, 0);
v_nextMacroScope_468_ = lean_ctor_get(v___x_465_, 1);
v_ngen_469_ = lean_ctor_get(v___x_465_, 2);
v_auxDeclNGen_470_ = lean_ctor_get(v___x_465_, 3);
v_cache_471_ = lean_ctor_get(v___x_465_, 5);
v_messages_472_ = lean_ctor_get(v___x_465_, 6);
v_infoState_473_ = lean_ctor_get(v___x_465_, 7);
v_snapshotTasks_474_ = lean_ctor_get(v___x_465_, 8);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_493_ == 0)
{
v___x_476_ = v___x_465_;
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snapshotTasks_474_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_472_);
lean_inc(v_cache_471_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_470_);
lean_inc(v_ngen_469_);
lean_inc(v_nextMacroScope_468_);
lean_inc(v_env_467_);
lean_dec(v___x_465_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint64_t v_tid_478_; lean_object* v_traces_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_492_; 
v_tid_478_ = lean_ctor_get_uint64(v_traceState_466_, sizeof(void*)*1);
v_traces_479_ = lean_ctor_get(v_traceState_466_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_traceState_466_);
if (v_isSharedCheck_492_ == 0)
{
v___x_481_ = v_traceState_466_;
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_traces_479_);
lean_dec(v_traceState_466_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_427_, v_traces_479_);
lean_dec_ref(v_traces_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set_uint64(v_reuseFailAlloc_491_, sizeof(void*)*1, v_tid_478_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_485_);
v___x_487_ = v___x_476_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_env_467_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_nextMacroScope_468_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_ngen_469_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_cache_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 7, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 8, v_snapshotTasks_474_);
v___x_487_ = v_reuseFailAlloc_490_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_st_ref_set(v___y_433_, v___x_487_);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(v_fst_435_);
return v___x_489_;
}
}
}
}
}
else
{
goto v___jp_458_;
}
}
else
{
goto v___jp_458_;
}
}
v___jp_494_:
{
double v___x_496_; double v___x_497_; double v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_unbox_float(v_snd_444_);
v___x_497_ = lean_unbox_float(v_fst_443_);
v___x_498_ = lean_float_sub(v___x_496_, v___x_497_);
v___x_499_ = lean_float_decLt(v___y_495_, v___x_498_);
v___y_464_ = v___x_499_;
goto v___jp_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2___boxed(lean_object* v_cls_510_, lean_object* v_collapsed_511_, lean_object* v_tag_512_, lean_object* v_opts_513_, lean_object* v_clsEnabled_514_, lean_object* v_oldTraces_515_, lean_object* v_msg_516_, lean_object* v_resStartStop_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_collapsed_boxed_523_; uint8_t v_clsEnabled_boxed_524_; lean_object* v_res_525_; 
v_collapsed_boxed_523_ = lean_unbox(v_collapsed_511_);
v_clsEnabled_boxed_524_ = lean_unbox(v_clsEnabled_514_);
v_res_525_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2(v_cls_510_, v_collapsed_boxed_523_, v_tag_512_, v_opts_513_, v_clsEnabled_boxed_524_, v_oldTraces_515_, v_msg_516_, v_resStartStop_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_opts_513_);
return v_res_525_;
}
}
static double _init_l_Lean_mkCasesOn___closed__4(void){
_start:
{
lean_object* v___x_532_; double v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(1000000000u);
v___x_533_ = lean_float_of_nat(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_mkCasesOn___closed__7(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_538_ = ((lean_object*)(l_Lean_mkCasesOn___closed__6));
v___x_539_ = l_Lean_Name_append(v___x_538_, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_options_546_; lean_object* v_inheritedTraceOptions_547_; uint8_t v_hasTrace_548_; lean_object* v_name_549_; uint8_t v___x_550_; 
v_options_546_ = lean_ctor_get(v_a_543_, 2);
v_inheritedTraceOptions_547_ = lean_ctor_get(v_a_543_, 13);
v_hasTrace_548_ = lean_ctor_get_uint8(v_options_546_, sizeof(void*)*1);
lean_inc(v_declName_540_);
v_name_549_ = l_Lean_mkCasesOnName(v_declName_540_);
v___x_550_ = lean_bool_not(v_hasTrace_548_);
if (v___x_550_ == 0)
{
lean_object* v___f_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___y_556_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v_a_559_; lean_object* v___y_572_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v_a_575_; lean_object* v___y_578_; lean_object* v___y_579_; uint8_t v___y_580_; lean_object* v___y_581_; lean_object* v___y_592_; lean_object* v___y_593_; uint8_t v___y_594_; lean_object* v_a_595_; lean_object* v___y_605_; lean_object* v___y_606_; uint8_t v___y_607_; lean_object* v_a_608_; lean_object* v___y_611_; lean_object* v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; uint8_t v___y_625_; uint8_t v_a_723_; 
lean_inc(v_declName_540_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_551_, 0, v_declName_540_);
v___x_552_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_553_ = 1;
v___x_554_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
if (v_hasTrace_548_ == 0)
{
v_a_723_ = v_hasTrace_548_;
goto v___jp_722_;
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_obj_once(&l_Lean_mkCasesOn___closed__7, &l_Lean_mkCasesOn___closed__7_once, _init_l_Lean_mkCasesOn___closed__7);
v___x_779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_547_, v_options_546_, v___x_778_);
if (v___x_779_ == 0)
{
v_a_723_ = v___x_779_;
goto v___jp_722_;
}
else
{
v___y_625_ = v___x_779_;
goto v___jp_624_;
}
}
v___jp_555_:
{
lean_object* v___x_560_; double v___x_561_; double v___x_562_; double v___x_563_; double v___x_564_; double v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_560_ = lean_io_mono_nanos_now();
v___x_561_ = lean_float_of_nat(v___y_558_);
v___x_562_ = lean_float_once(&l_Lean_mkCasesOn___closed__4, &l_Lean_mkCasesOn___closed__4_once, _init_l_Lean_mkCasesOn___closed__4);
v___x_563_ = lean_float_div(v___x_561_, v___x_562_);
v___x_564_ = lean_float_of_nat(v___x_560_);
v___x_565_ = lean_float_div(v___x_564_, v___x_562_);
v___x_566_ = lean_box_float(v___x_563_);
v___x_567_ = lean_box_float(v___x_565_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_559_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2(v___x_552_, v___x_553_, v___x_554_, v_options_546_, v___y_557_, v___y_556_, v___f_551_, v___x_569_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_570_;
}
v___jp_571_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_a_575_);
v___y_556_ = v___y_572_;
v___y_557_ = v___y_574_;
v___y_558_ = v___y_573_;
v_a_559_ = v___x_576_;
goto v___jp_555_;
}
v___jp_577_:
{
if (lean_obj_tag(v___y_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___y_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___y_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___y_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___y_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 1);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v___y_556_ = v___y_578_;
v___y_557_ = v___y_580_;
v___y_558_ = v___y_579_;
v_a_559_ = v___x_587_;
goto v___jp_555_;
}
}
}
else
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___y_581_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___y_581_, 1);
v___y_572_ = v___y_578_;
v___y_573_ = v___y_579_;
v___y_574_ = v___y_580_;
v_a_575_ = v_a_590_;
goto v___jp_571_;
}
}
v___jp_591_:
{
lean_object* v___x_596_; double v___x_597_; double v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_596_ = lean_io_get_num_heartbeats();
v___x_597_ = lean_float_of_nat(v___y_592_);
v___x_598_ = lean_float_of_nat(v___x_596_);
v___x_599_ = lean_box_float(v___x_597_);
v___x_600_ = lean_box_float(v___x_598_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_a_595_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2(v___x_552_, v___x_553_, v___x_554_, v_options_546_, v___y_594_, v___y_593_, v___f_551_, v___x_602_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_603_;
}
v___jp_604_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_a_608_);
v___y_592_ = v___y_605_;
v___y_593_ = v___y_606_;
v___y_594_ = v___y_607_;
v_a_595_ = v___x_609_;
goto v___jp_591_;
}
v___jp_610_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___y_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___y_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___y_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 1);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v___y_592_ = v___y_611_;
v___y_593_ = v___y_612_;
v___y_594_ = v___y_613_;
v_a_595_ = v___x_620_;
goto v___jp_591_;
}
}
}
else
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___y_614_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___y_614_, 1);
v___y_605_ = v___y_611_;
v___y_606_ = v___y_612_;
v___y_607_ = v___y_613_;
v_a_608_ = v_a_623_;
goto v___jp_604_;
}
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v_a_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_626_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__0___redArg(v_a_544_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v___x_628_ = l_Lean_trace_profiler_useHeartbeats;
v___x_629_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(v_options_546_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_env_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = lean_io_mono_nanos_now();
v___x_631_ = lean_st_ref_get(v_a_544_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v___x_633_ = lean_elab_environment_to_kernel_env(v_env_632_);
v___x_634_ = lean_mk_cases_on(v___x_633_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_635_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v___x_634_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_addDecl(v_a_636_, v___x_629_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_env_640_; lean_object* v_nextMacroScope_641_; lean_object* v_ngen_642_; lean_object* v_auxDeclNGen_643_; lean_object* v_traceState_644_; lean_object* v_messages_645_; lean_object* v_infoState_646_; lean_object* v_snapshotTasks_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref_known(v___x_637_, 1);
lean_inc(v_name_549_);
v___x_638_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_638_);
v___x_639_ = lean_st_ref_take(v_a_544_);
v_env_640_ = lean_ctor_get(v___x_639_, 0);
v_nextMacroScope_641_ = lean_ctor_get(v___x_639_, 1);
v_ngen_642_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_643_ = lean_ctor_get(v___x_639_, 3);
v_traceState_644_ = lean_ctor_get(v___x_639_, 4);
v_messages_645_ = lean_ctor_get(v___x_639_, 6);
v_infoState_646_ = lean_ctor_get(v___x_639_, 7);
v_snapshotTasks_647_ = lean_ctor_get(v___x_639_, 8);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_639_, 5);
lean_dec(v_unused_674_);
v___x_649_ = v___x_639_;
v_isShared_650_ = v_isSharedCheck_673_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_snapshotTasks_647_);
lean_inc(v_infoState_646_);
lean_inc(v_messages_645_);
lean_inc(v_traceState_644_);
lean_inc(v_auxDeclNGen_643_);
lean_inc(v_ngen_642_);
lean_inc(v_nextMacroScope_641_);
lean_inc(v_env_640_);
lean_dec(v___x_639_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_673_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_inc(v_name_549_);
v___x_651_ = l_Lean_markAuxRecursor(v_env_640_, v_name_549_);
v___x_652_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 5, v___x_652_);
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_nextMacroScope_641_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ngen_642_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_auxDeclNGen_643_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_traceState_644_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v_messages_645_);
lean_ctor_set(v_reuseFailAlloc_672_, 7, v_infoState_646_);
lean_ctor_set(v_reuseFailAlloc_672_, 8, v_snapshotTasks_647_);
v___x_654_ = v_reuseFailAlloc_672_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_mctx_657_; lean_object* v_zetaDeltaFVarIds_658_; lean_object* v_postponed_659_; lean_object* v_diag_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
v___x_655_ = lean_st_ref_set(v_a_544_, v___x_654_);
v___x_656_ = lean_st_ref_take(v_a_542_);
v_mctx_657_ = lean_ctor_get(v___x_656_, 0);
v_zetaDeltaFVarIds_658_ = lean_ctor_get(v___x_656_, 2);
v_postponed_659_ = lean_ctor_get(v___x_656_, 3);
v_diag_660_ = lean_ctor_get(v___x_656_, 4);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_656_, 1);
lean_dec(v_unused_671_);
v___x_662_ = v___x_656_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_diag_660_);
lean_inc(v_postponed_659_);
lean_inc(v_zetaDeltaFVarIds_658_);
lean_inc(v_mctx_657_);
lean_dec(v___x_656_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_mctx_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_zetaDeltaFVarIds_658_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_postponed_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_diag_660_);
v___x_666_ = v_reuseFailAlloc_669_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_st_ref_set(v_a_542_, v___x_666_);
v___x_668_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
v___y_578_ = v_a_627_;
v___y_579_ = v___x_630_;
v___y_580_ = v___y_625_;
v___y_581_ = v___x_668_;
goto v___jp_577_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
v___y_578_ = v_a_627_;
v___y_579_ = v___x_630_;
v___y_580_ = v___y_625_;
v___y_581_ = v___x_637_;
goto v___jp_577_;
}
}
else
{
lean_object* v_a_675_; 
lean_dec(v_name_549_);
v_a_675_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_635_, 1);
v___y_572_ = v_a_627_;
v___y_573_ = v___x_630_;
v___y_574_ = v___y_625_;
v_a_575_ = v_a_675_;
goto v___jp_571_;
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_env_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_io_get_num_heartbeats();
v___x_677_ = lean_st_ref_get(v_a_544_);
v_env_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_env_678_);
lean_dec(v___x_677_);
v___x_679_ = lean_elab_environment_to_kernel_env(v_env_678_);
v___x_680_ = lean_mk_cases_on(v___x_679_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_681_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v___x_680_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = l_Lean_addDecl(v_a_682_, v___x_550_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_env_686_; lean_object* v_nextMacroScope_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_traceState_690_; lean_object* v_messages_691_; lean_object* v_infoState_692_; lean_object* v_snapshotTasks_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref_known(v___x_683_, 1);
lean_inc(v_name_549_);
v___x_684_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_684_);
v___x_685_ = lean_st_ref_take(v_a_544_);
v_env_686_ = lean_ctor_get(v___x_685_, 0);
v_nextMacroScope_687_ = lean_ctor_get(v___x_685_, 1);
v_ngen_688_ = lean_ctor_get(v___x_685_, 2);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_685_, 3);
v_traceState_690_ = lean_ctor_get(v___x_685_, 4);
v_messages_691_ = lean_ctor_get(v___x_685_, 6);
v_infoState_692_ = lean_ctor_get(v___x_685_, 7);
v_snapshotTasks_693_ = lean_ctor_get(v___x_685_, 8);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_685_, 5);
lean_dec(v_unused_720_);
v___x_695_ = v___x_685_;
v_isShared_696_ = v_isSharedCheck_719_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snapshotTasks_693_);
lean_inc(v_infoState_692_);
lean_inc(v_messages_691_);
lean_inc(v_traceState_690_);
lean_inc(v_auxDeclNGen_689_);
lean_inc(v_ngen_688_);
lean_inc(v_nextMacroScope_687_);
lean_inc(v_env_686_);
lean_dec(v___x_685_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_719_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_inc(v_name_549_);
v___x_697_ = l_Lean_markAuxRecursor(v_env_686_, v_name_549_);
v___x_698_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 5, v___x_698_);
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_nextMacroScope_687_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_ngen_688_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_auxDeclNGen_689_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_traceState_690_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_messages_691_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_infoState_692_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_snapshotTasks_693_);
v___x_700_ = v_reuseFailAlloc_718_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_mctx_703_; lean_object* v_zetaDeltaFVarIds_704_; lean_object* v_postponed_705_; lean_object* v_diag_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_716_; 
v___x_701_ = lean_st_ref_set(v_a_544_, v___x_700_);
v___x_702_ = lean_st_ref_take(v_a_542_);
v_mctx_703_ = lean_ctor_get(v___x_702_, 0);
v_zetaDeltaFVarIds_704_ = lean_ctor_get(v___x_702_, 2);
v_postponed_705_ = lean_ctor_get(v___x_702_, 3);
v_diag_706_ = lean_ctor_get(v___x_702_, 4);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_702_, 1);
lean_dec(v_unused_717_);
v___x_708_ = v___x_702_;
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_diag_706_);
lean_inc(v_postponed_705_);
lean_inc(v_zetaDeltaFVarIds_704_);
lean_inc(v_mctx_703_);
lean_dec(v___x_702_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_mctx_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_zetaDeltaFVarIds_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_postponed_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_diag_706_);
v___x_712_ = v_reuseFailAlloc_715_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_st_ref_set(v_a_542_, v___x_712_);
v___x_714_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
v___y_611_ = v___x_676_;
v___y_612_ = v_a_627_;
v___y_613_ = v___y_625_;
v___y_614_ = v___x_714_;
goto v___jp_610_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
v___y_611_ = v___x_676_;
v___y_612_ = v_a_627_;
v___y_613_ = v___y_625_;
v___y_614_ = v___x_683_;
goto v___jp_610_;
}
}
else
{
lean_object* v_a_721_; 
lean_dec(v_name_549_);
v_a_721_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_681_, 1);
v___y_605_ = v___x_676_;
v___y_606_ = v_a_627_;
v___y_607_ = v___y_625_;
v_a_608_ = v_a_721_;
goto v___jp_604_;
}
}
}
v___jp_722_:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = l_Lean_trace_profiler;
v___x_725_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__1(v_options_546_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v_env_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v___f_551_);
v___x_726_ = lean_st_ref_get(v_a_544_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v___x_728_ = lean_elab_environment_to_kernel_env(v_env_727_);
v___x_729_ = lean_mk_cases_on(v___x_728_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_730_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v___x_729_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_addDecl(v_a_731_, v___x_725_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_env_735_; lean_object* v_nextMacroScope_736_; lean_object* v_ngen_737_; lean_object* v_auxDeclNGen_738_; lean_object* v_traceState_739_; lean_object* v_messages_740_; lean_object* v_infoState_741_; lean_object* v_snapshotTasks_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref_known(v___x_732_, 1);
lean_inc(v_name_549_);
v___x_733_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_733_);
v___x_734_ = lean_st_ref_take(v_a_544_);
v_env_735_ = lean_ctor_get(v___x_734_, 0);
v_nextMacroScope_736_ = lean_ctor_get(v___x_734_, 1);
v_ngen_737_ = lean_ctor_get(v___x_734_, 2);
v_auxDeclNGen_738_ = lean_ctor_get(v___x_734_, 3);
v_traceState_739_ = lean_ctor_get(v___x_734_, 4);
v_messages_740_ = lean_ctor_get(v___x_734_, 6);
v_infoState_741_ = lean_ctor_get(v___x_734_, 7);
v_snapshotTasks_742_ = lean_ctor_get(v___x_734_, 8);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_734_, 5);
lean_dec(v_unused_769_);
v___x_744_ = v___x_734_;
v_isShared_745_ = v_isSharedCheck_768_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snapshotTasks_742_);
lean_inc(v_infoState_741_);
lean_inc(v_messages_740_);
lean_inc(v_traceState_739_);
lean_inc(v_auxDeclNGen_738_);
lean_inc(v_ngen_737_);
lean_inc(v_nextMacroScope_736_);
lean_inc(v_env_735_);
lean_dec(v___x_734_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_768_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
lean_inc(v_name_549_);
v___x_746_ = l_Lean_markAuxRecursor(v_env_735_, v_name_549_);
v___x_747_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 5, v___x_747_);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_nextMacroScope_736_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_ngen_737_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_auxDeclNGen_738_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_traceState_739_);
lean_ctor_set(v_reuseFailAlloc_767_, 5, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_767_, 6, v_messages_740_);
lean_ctor_set(v_reuseFailAlloc_767_, 7, v_infoState_741_);
lean_ctor_set(v_reuseFailAlloc_767_, 8, v_snapshotTasks_742_);
v___x_749_ = v_reuseFailAlloc_767_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_mctx_752_; lean_object* v_zetaDeltaFVarIds_753_; lean_object* v_postponed_754_; lean_object* v_diag_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_765_; 
v___x_750_ = lean_st_ref_set(v_a_544_, v___x_749_);
v___x_751_ = lean_st_ref_take(v_a_542_);
v_mctx_752_ = lean_ctor_get(v___x_751_, 0);
v_zetaDeltaFVarIds_753_ = lean_ctor_get(v___x_751_, 2);
v_postponed_754_ = lean_ctor_get(v___x_751_, 3);
v_diag_755_ = lean_ctor_get(v___x_751_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_751_, 1);
lean_dec(v_unused_766_);
v___x_757_ = v___x_751_;
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_diag_755_);
lean_inc(v_postponed_754_);
lean_inc(v_zetaDeltaFVarIds_753_);
lean_inc(v_mctx_752_);
lean_dec(v___x_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_mctx_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_zetaDeltaFVarIds_753_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_postponed_754_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_diag_755_);
v___x_761_ = v_reuseFailAlloc_764_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_st_ref_set(v_a_542_, v___x_761_);
v___x_763_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
return v___x_763_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
return v___x_732_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_name_549_);
v_a_770_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_730_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_730_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
v___y_625_ = v_a_723_;
goto v___jp_624_;
}
}
}
else
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_780_ = lean_st_ref_get(v_a_544_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = lean_elab_environment_to_kernel_env(v_env_781_);
v___x_783_ = lean_mk_cases_on(v___x_782_, v_declName_540_);
lean_dec(v_declName_540_);
v___x_784_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v___x_783_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = 0;
v___x_787_ = l_Lean_addDecl(v_a_785_, v___x_786_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_env_790_; lean_object* v_nextMacroScope_791_; lean_object* v_ngen_792_; lean_object* v_auxDeclNGen_793_; lean_object* v_traceState_794_; lean_object* v_messages_795_; lean_object* v_infoState_796_; lean_object* v_snapshotTasks_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref_known(v___x_787_, 1);
lean_inc(v_name_549_);
v___x_788_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4(v_name_549_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_788_);
v___x_789_ = lean_st_ref_take(v_a_544_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
v_nextMacroScope_791_ = lean_ctor_get(v___x_789_, 1);
v_ngen_792_ = lean_ctor_get(v___x_789_, 2);
v_auxDeclNGen_793_ = lean_ctor_get(v___x_789_, 3);
v_traceState_794_ = lean_ctor_get(v___x_789_, 4);
v_messages_795_ = lean_ctor_get(v___x_789_, 6);
v_infoState_796_ = lean_ctor_get(v___x_789_, 7);
v_snapshotTasks_797_ = lean_ctor_get(v___x_789_, 8);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_789_, 5);
lean_dec(v_unused_824_);
v___x_799_ = v___x_789_;
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snapshotTasks_797_);
lean_inc(v_infoState_796_);
lean_inc(v_messages_795_);
lean_inc(v_traceState_794_);
lean_inc(v_auxDeclNGen_793_);
lean_inc(v_ngen_792_);
lean_inc(v_nextMacroScope_791_);
lean_inc(v_env_790_);
lean_dec(v___x_789_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_name_549_);
v___x_801_ = l_Lean_markAuxRecursor(v_env_790_, v_name_549_);
v___x_802_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__2);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 5, v___x_802_);
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_804_ = v___x_799_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_nextMacroScope_791_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_ngen_792_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_auxDeclNGen_793_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_traceState_794_);
lean_ctor_set(v_reuseFailAlloc_822_, 5, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_822_, 6, v_messages_795_);
lean_ctor_set(v_reuseFailAlloc_822_, 7, v_infoState_796_);
lean_ctor_set(v_reuseFailAlloc_822_, 8, v_snapshotTasks_797_);
v___x_804_ = v_reuseFailAlloc_822_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_mctx_807_; lean_object* v_zetaDeltaFVarIds_808_; lean_object* v_postponed_809_; lean_object* v_diag_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_820_; 
v___x_805_ = lean_st_ref_set(v_a_544_, v___x_804_);
v___x_806_ = lean_st_ref_take(v_a_542_);
v_mctx_807_ = lean_ctor_get(v___x_806_, 0);
v_zetaDeltaFVarIds_808_ = lean_ctor_get(v___x_806_, 2);
v_postponed_809_ = lean_ctor_get(v___x_806_, 3);
v_diag_810_ = lean_ctor_get(v___x_806_, 4);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_806_, 1);
lean_dec(v_unused_821_);
v___x_812_ = v___x_806_;
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_diag_810_);
lean_inc(v_postponed_809_);
lean_inc(v_zetaDeltaFVarIds_808_);
lean_inc(v_mctx_807_);
lean_dec(v___x_806_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg___closed__3);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_mctx_807_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_zetaDeltaFVarIds_808_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_postponed_809_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_diag_810_);
v___x_816_ = v_reuseFailAlloc_819_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_st_ref_set(v_a_542_, v___x_816_);
v___x_818_ = l_Lean_enableRealizationsForConst(v_name_549_, v_a_543_, v_a_544_);
return v___x_818_;
}
}
}
}
}
else
{
lean_dec(v_name_549_);
return v___x_787_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_name_549_);
v_a_825_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_784_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_784_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_mkCasesOn(v_declName_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3(lean_object* v_00_u03b1_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___redArg(v_x_841_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3___boxed(lean_object* v_00_u03b1_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__2_spec__3(v_00_u03b1_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3(lean_object* v_00_u03b1_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___redArg(v_x_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3___boxed(lean_object* v_00_u03b1_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3(v_00_u03b1_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object* v_declName_872_, uint8_t v_s_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___redArg(v_declName_872_, v_s_873_, v___y_875_, v___y_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object* v_declName_880_, lean_object* v_s_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v_s_boxed_887_; lean_object* v_res_888_; 
v_s_boxed_887_ = lean_unbox(v_s_881_);
v_res_888_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__4_spec__9(v_declName_880_, v_s_boxed_887_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11(lean_object* v_00_u03b1_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___redArg();
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b1_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__11(v_00_u03b1_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7(lean_object* v_00_u03b1_903_, lean_object* v_ex_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___redArg(v_ex_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7___boxed(lean_object* v_00_u03b1_911_, lean_object* v_ex_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7(v_00_u03b1_911_, v_ex_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_919_, lean_object* v_msg_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___redArg(v_msg_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_927_, lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__3_spec__7_spec__10(v_00_u03b1_927_, v_msg_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_996_ = 0;
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_998_ = l_Lean_registerTraceClass(v___x_995_, v___x_996_, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_1000_;
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

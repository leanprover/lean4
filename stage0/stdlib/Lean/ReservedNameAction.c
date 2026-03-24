// Lean compiler output
// Module: Lean.ReservedNameAction
// Imports: public import Init.Control.Do public import Lean.CoreM
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_initializing();
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_array_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
static const lean_string_object l_Lean_registerReservedNameAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 109, .m_capacity = 109, .m_length = 108, .m_data = "failed to register reserved name action, this kind of extension can only be registered during initialization"};
static const lean_object* l_Lean_registerReservedNameAction___closed__0 = (const lean_object*)&l_Lean_registerReservedNameAction___closed__0_value;
static lean_once_cell_t l_Lean_registerReservedNameAction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerReservedNameAction___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "executeReservedNameAction for "};
static const lean_object* l_Lean_executeReservedNameAction___lam__0___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_executeReservedNameAction___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l_Lean_executeReservedNameAction___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__0_value;
static const lean_ctor_object l_Lean_executeReservedNameAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_executeReservedNameAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l_Lean_executeReservedNameAction___closed__1 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__1_value;
static const lean_string_object l_Lean_executeReservedNameAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_executeReservedNameAction___closed__2 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__2_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_executeReservedNameAction___closed__3;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Failed to realize constant "};
static const lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0 = (const lean_object*)&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0_value;
static lean_once_cell_t l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1;
static const lean_string_object l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2 = (const lean_object*)&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2_value;
static lean_once_cell_t l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Ambiguous identifier `"};
static const lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0 = (const lean_object*)&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1;
static const lean_string_object l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`; possible interpretations: "};
static const lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2 = (const lean_object*)&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0_value;
static const lean_string_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected identifier"};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value)}};
static const lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_realizeGlobalConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_realizeGlobalConstCore___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_realizeGlobalConst___closed__0 = (const lean_object*)&l_Lean_realizeGlobalConst___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object*);
static const lean_string_object l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.ResolveName"};
static const lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0 = (const lean_object*)&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0_value;
static const lean_string_object l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.ensureNonAmbiguous"};
static const lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1 = (const lean_object*)&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1_value;
static const lean_string_object l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2 = (const lean_object*)&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3;
static const lean_string_object l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous identifier `"};
static const lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4 = (const lean_object*)&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4_value;
static const lean_string_object l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`, possible interpretations: "};
static const lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5 = (const lean_object*)&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l_Lean_executeReservedNameAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 77, 113, 63, 96, 174, 5, 36)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 134, 188, 99, 68, 49, 54, 53)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 68, 123, 165, 47, 200, 95, 7)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 190, 58, 198, 41, 48, 224, 245)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 56, 43, 39, 224, 149, 205, 64)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 237, 47, 226, 18, 254, 185, 143)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value),((lean_object*)&l_Lean_executeReservedNameAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 211, 52, 116, 118, 178, 20, 72)}};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_));
v___x_5_ = lean_st_mk_ref(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
return v_res_8_;
}
}
static lean_object* _init_l_Lean_registerReservedNameAction___closed__1(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_registerReservedNameAction___closed__0));
v___x_11_ = lean_mk_io_user_error(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction(lean_object* v_act_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_initializing();
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_31_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_31_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; 
v___x_19_ = lean_unbox(v_a_15_);
lean_dec(v_a_15_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_22_; 
lean_dec_ref(v_act_12_);
v___x_20_ = lean_obj_once(&l_Lean_registerReservedNameAction___closed__1, &l_Lean_registerReservedNameAction___closed__1_once, _init_l_Lean_registerReservedNameAction___closed__1);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 1);
lean_ctor_set(v___x_17_, 0, v___x_20_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_24_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_25_ = lean_st_ref_take(v___x_24_);
v___x_26_ = lean_array_push(v___x_25_, v_act_12_);
v___x_27_ = lean_st_ref_set(v___x_24_, v___x_26_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_27_);
v___x_29_ = v___x_17_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec_ref(v_act_12_);
v_a_32_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_14_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_14_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction___boxed(lean_object* v_act_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_registerReservedNameAction(v_act_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object* v_cls_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_options_49_; uint8_t v_hasTrace_50_; 
v_options_49_ = lean_ctor_get(v___y_47_, 2);
v_hasTrace_50_ = lean_ctor_get_uint8(v_options_49_, sizeof(void*)*1);
if (v_hasTrace_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_cls_46_);
v___x_51_ = lean_box(v_hasTrace_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_inheritedTraceOptions_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_inheritedTraceOptions_53_ = lean_ctor_get(v___y_47_, 13);
v___x_54_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1));
v___x_55_ = l_Lean_Name_append(v___x_54_, v_cls_46_);
v___x_56_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_53_, v_options_49_, v___x_55_);
lean_dec(v___x_55_);
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object* v_cls_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(v_cls_59_, v___y_60_);
lean_dec_ref(v___y_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1(lean_object* v_cls_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(v_cls_63_, v___y_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v_cls_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1(v_cls_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_72_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(32u);
v___x_74_ = lean_mk_empty_array_with_capacity(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = ((size_t)5ULL);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_unsigned_to_nat(32u);
v___x_79_ = lean_mk_empty_array_with_capacity(v___x_78_);
v___x_80_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__0);
v___x_81_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_77_);
lean_ctor_set(v___x_81_, 3, v___x_77_);
lean_ctor_set_usize(v___x_81_, 4, v___x_76_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; lean_object* v_traceState_85_; lean_object* v_traces_86_; lean_object* v___x_87_; lean_object* v_traceState_88_; lean_object* v_env_89_; lean_object* v_nextMacroScope_90_; lean_object* v_ngen_91_; lean_object* v_auxDeclNGen_92_; lean_object* v_cache_93_; lean_object* v_messages_94_; lean_object* v_infoState_95_; lean_object* v_snapshotTasks_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_115_; 
v___x_84_ = lean_st_ref_get(v___y_82_);
v_traceState_85_ = lean_ctor_get(v___x_84_, 4);
lean_inc_ref(v_traceState_85_);
lean_dec(v___x_84_);
v_traces_86_ = lean_ctor_get(v_traceState_85_, 0);
lean_inc_ref(v_traces_86_);
lean_dec_ref(v_traceState_85_);
v___x_87_ = lean_st_ref_take(v___y_82_);
v_traceState_88_ = lean_ctor_get(v___x_87_, 4);
v_env_89_ = lean_ctor_get(v___x_87_, 0);
v_nextMacroScope_90_ = lean_ctor_get(v___x_87_, 1);
v_ngen_91_ = lean_ctor_get(v___x_87_, 2);
v_auxDeclNGen_92_ = lean_ctor_get(v___x_87_, 3);
v_cache_93_ = lean_ctor_get(v___x_87_, 5);
v_messages_94_ = lean_ctor_get(v___x_87_, 6);
v_infoState_95_ = lean_ctor_get(v___x_87_, 7);
v_snapshotTasks_96_ = lean_ctor_get(v___x_87_, 8);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_115_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_115_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snapshotTasks_96_);
lean_inc(v_infoState_95_);
lean_inc(v_messages_94_);
lean_inc(v_cache_93_);
lean_inc(v_traceState_88_);
lean_inc(v_auxDeclNGen_92_);
lean_inc(v_ngen_91_);
lean_inc(v_nextMacroScope_90_);
lean_inc(v_env_89_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_115_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
uint64_t v_tid_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_113_; 
v_tid_100_ = lean_ctor_get_uint64(v_traceState_88_, sizeof(void*)*1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_traceState_88_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_traceState_88_, 0);
lean_dec(v_unused_114_);
v___x_102_ = v_traceState_88_;
v_isShared_103_ = v_isSharedCheck_113_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_traceState_88_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_113_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___closed__1);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_104_);
lean_ctor_set_uint64(v_reuseFailAlloc_112_, sizeof(void*)*1, v_tid_100_);
v___x_106_ = v_reuseFailAlloc_112_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_106_);
v___x_108_ = v___x_98_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_env_89_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_nextMacroScope_90_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v_ngen_91_);
lean_ctor_set(v_reuseFailAlloc_111_, 3, v_auxDeclNGen_92_);
lean_ctor_set(v_reuseFailAlloc_111_, 4, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_111_, 5, v_cache_93_);
lean_ctor_set(v_reuseFailAlloc_111_, 6, v_messages_94_);
lean_ctor_set(v_reuseFailAlloc_111_, 7, v_infoState_95_);
lean_ctor_set(v_reuseFailAlloc_111_, 8, v_snapshotTasks_96_);
v___x_108_ = v_reuseFailAlloc_111_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_st_ref_set(v___y_82_, v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v_traces_86_);
return v___x_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg___boxed(lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(v___y_116_);
lean_dec(v___y_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2(lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(v___y_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2(v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
lean_object* v_name_129_; lean_object* v_defValue_130_; lean_object* v_map_131_; lean_object* v___x_132_; 
v_name_129_ = lean_ctor_get(v_opt_128_, 0);
v_defValue_130_ = lean_ctor_get(v_opt_128_, 1);
v_map_131_ = lean_ctor_get(v_opts_127_, 0);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_131_, v_name_129_);
if (lean_obj_tag(v___x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = lean_unbox(v_defValue_130_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v___x_132_);
if (lean_obj_tag(v_val_134_) == 1)
{
uint8_t v_v_135_; 
v_v_135_ = lean_ctor_get_uint8(v_val_134_, 0);
lean_dec_ref(v_val_134_);
return v_v_135_;
}
else
{
uint8_t v___x_136_; 
lean_dec(v_val_134_);
v___x_136_ = lean_unbox(v_defValue_130_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_opts_137_, v_opt_138_);
lean_dec_ref(v_opt_138_);
lean_dec_ref(v_opts_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_executeReservedNameAction___lam__0___closed__0));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object* v_name_144_, lean_object* v_x_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = lean_obj_once(&l_Lean_executeReservedNameAction___lam__0___closed__1, &l_Lean_executeReservedNameAction___lam__0___closed__1_once, _init_l_Lean_executeReservedNameAction___lam__0___closed__1);
v___x_150_ = l_Lean_MessageData_ofName(v_name_144_);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object* v_name_153_, lean_object* v_x_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_executeReservedNameAction___lam__0(v_name_153_, v_x_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec_ref(v_x_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_159_, lean_object* v_as_160_, size_t v_i_161_, size_t v_stop_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_eq(v_i_161_, v_stop_162_);
if (v___x_166_ == 0)
{
lean_object* v___x_4539__overap_167_; lean_object* v___x_168_; 
v___x_4539__overap_167_ = lean_array_uget_borrowed(v_as_160_, v_i_161_);
lean_inc(v___x_4539__overap_167_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v_name_159_);
v___x_168_ = lean_apply_4(v___x_4539__overap_167_, v_name_159_, v___y_163_, v___y_164_, lean_box(0));
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_180_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_180_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___x_173_; 
v___x_173_ = lean_unbox(v_a_169_);
if (v___x_173_ == 0)
{
size_t v___x_174_; size_t v___x_175_; 
lean_del_object(v___x_171_);
lean_dec(v_a_169_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_i_161_, v___x_174_);
v_i_161_ = v___x_175_;
goto _start;
}
else
{
lean_object* v___x_178_; 
lean_dec(v_name_159_);
if (v_isShared_172_ == 0)
{
v___x_178_ = v___x_171_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_169_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_dec(v_name_159_);
return v___x_168_;
}
}
else
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_name_159_);
v___x_181_ = 0;
v___x_182_ = lean_box(v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_184_, lean_object* v_as_185_, lean_object* v_i_186_, lean_object* v_stop_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
size_t v_i_boxed_191_; size_t v_stop_boxed_192_; lean_object* v_res_193_; 
v_i_boxed_191_ = lean_unbox_usize(v_i_186_);
lean_dec(v_i_186_);
v_stop_boxed_192_ = lean_unbox_usize(v_stop_187_);
lean_dec(v_stop_187_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_184_, v_as_185_, v_i_boxed_191_, v_stop_boxed_192_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v_as_185_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(lean_object* v_opts_194_, lean_object* v_opt_195_){
_start:
{
lean_object* v_name_196_; lean_object* v_defValue_197_; lean_object* v_map_198_; lean_object* v___x_199_; 
v_name_196_ = lean_ctor_get(v_opt_195_, 0);
v_defValue_197_ = lean_ctor_get(v_opt_195_, 1);
v_map_198_ = lean_ctor_get(v_opts_194_, 0);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_198_, v_name_196_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_inc(v_defValue_197_);
return v_defValue_197_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref(v___x_199_);
if (lean_obj_tag(v_val_200_) == 3)
{
lean_object* v_v_201_; 
v_v_201_ = lean_ctor_get(v_val_200_, 0);
lean_inc(v_v_201_);
lean_dec_ref(v_val_200_);
return v_v_201_;
}
else
{
lean_dec(v_val_200_);
lean_inc(v_defValue_197_);
return v_defValue_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7___boxed(lean_object* v_opts_202_, lean_object* v_opt_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(v_opts_202_, v_opt_203_);
lean_dec_ref(v_opt_203_);
lean_dec_ref(v_opts_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_x_205_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 1);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_215_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v_x_205_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v_x_205_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 0);
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg___boxed(lean_object* v_x_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_x_223_);
return v_res_225_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4(lean_object* v_e_226_){
_start:
{
if (lean_obj_tag(v_e_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 2;
return v___x_227_;
}
else
{
lean_object* v_a_228_; uint8_t v___x_229_; 
v_a_228_ = lean_ctor_get(v_e_226_, 0);
v___x_229_ = lean_unbox(v_a_228_);
if (v___x_229_ == 0)
{
uint8_t v___x_230_; 
v___x_230_ = 1;
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4___boxed(lean_object* v_e_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4(v_e_232_);
lean_dec_ref(v_e_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_ctor_set(v___x_240_, 3, v___x_238_);
lean_ctor_set(v___x_240_, 4, v___x_238_);
lean_ctor_set(v___x_240_, 5, v___x_238_);
lean_ctor_set(v___x_240_, 6, v___x_238_);
lean_ctor_set(v___x_240_, 7, v___x_238_);
lean_ctor_set(v___x_240_, 8, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_unsigned_to_nat(32u);
v___x_242_ = lean_mk_empty_array_with_capacity(v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4(void){
_start:
{
size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_244_ = ((size_t)5ULL);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_unsigned_to_nat(32u);
v___x_247_ = lean_mk_empty_array_with_capacity(v___x_246_);
v___x_248_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__3);
v___x_249_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_245_);
lean_ctor_set(v___x_249_, 3, v___x_245_);
lean_ctor_set_usize(v___x_249_, 4, v___x_244_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_box(1);
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__4);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__1);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_250_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(lean_object* v_msgData_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v_options_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
v_options_260_ = lean_ctor_get(v___y_255_, 2);
v___x_261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2);
v___x_262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5);
lean_inc_ref(v_options_260_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_259_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v_options_260_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_254_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v_msgData_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6(size_t v_sz_271_, size_t v_i_272_, lean_object* v_bs_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_lt(v_i_272_, v_sz_271_);
if (v___x_274_ == 0)
{
return v_bs_273_;
}
else
{
lean_object* v_v_275_; lean_object* v_msg_276_; lean_object* v___x_277_; lean_object* v_bs_x27_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v_v_275_ = lean_array_uget_borrowed(v_bs_273_, v_i_272_);
v_msg_276_ = lean_ctor_get(v_v_275_, 1);
lean_inc_ref(v_msg_276_);
v___x_277_ = lean_unsigned_to_nat(0u);
v_bs_x27_278_ = lean_array_uset(v_bs_273_, v_i_272_, v___x_277_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_272_, v___x_279_);
v___x_281_ = lean_array_uset(v_bs_x27_278_, v_i_272_, v_msg_276_);
v_i_272_ = v___x_280_;
v_bs_273_ = v___x_281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_283_, lean_object* v_i_284_, lean_object* v_bs_285_){
_start:
{
size_t v_sz_boxed_286_; size_t v_i_boxed_287_; lean_object* v_res_288_; 
v_sz_boxed_286_ = lean_unbox_usize(v_sz_283_);
lean_dec(v_sz_283_);
v_i_boxed_287_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6(v_sz_boxed_286_, v_i_boxed_287_, v_bs_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(lean_object* v_oldTraces_289_, lean_object* v_data_290_, lean_object* v_ref_291_, lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_fileName_296_; lean_object* v_fileMap_297_; lean_object* v_options_298_; lean_object* v_currRecDepth_299_; lean_object* v_maxRecDepth_300_; lean_object* v_ref_301_; lean_object* v_currNamespace_302_; lean_object* v_openDecls_303_; lean_object* v_initHeartbeats_304_; lean_object* v_maxHeartbeats_305_; lean_object* v_quotContext_306_; lean_object* v_currMacroScope_307_; uint8_t v_diag_308_; lean_object* v_cancelTk_x3f_309_; uint8_t v_suppressElabErrors_310_; lean_object* v_inheritedTraceOptions_311_; lean_object* v___x_312_; lean_object* v_traceState_313_; lean_object* v_traces_314_; lean_object* v_ref_315_; lean_object* v___x_316_; lean_object* v___x_317_; size_t v_sz_318_; size_t v___x_319_; lean_object* v___x_320_; lean_object* v_msg_321_; lean_object* v___x_322_; lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_360_; 
v_fileName_296_ = lean_ctor_get(v___y_293_, 0);
v_fileMap_297_ = lean_ctor_get(v___y_293_, 1);
v_options_298_ = lean_ctor_get(v___y_293_, 2);
v_currRecDepth_299_ = lean_ctor_get(v___y_293_, 3);
v_maxRecDepth_300_ = lean_ctor_get(v___y_293_, 4);
v_ref_301_ = lean_ctor_get(v___y_293_, 5);
v_currNamespace_302_ = lean_ctor_get(v___y_293_, 6);
v_openDecls_303_ = lean_ctor_get(v___y_293_, 7);
v_initHeartbeats_304_ = lean_ctor_get(v___y_293_, 8);
v_maxHeartbeats_305_ = lean_ctor_get(v___y_293_, 9);
v_quotContext_306_ = lean_ctor_get(v___y_293_, 10);
v_currMacroScope_307_ = lean_ctor_get(v___y_293_, 11);
v_diag_308_ = lean_ctor_get_uint8(v___y_293_, sizeof(void*)*14);
v_cancelTk_x3f_309_ = lean_ctor_get(v___y_293_, 12);
v_suppressElabErrors_310_ = lean_ctor_get_uint8(v___y_293_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_311_ = lean_ctor_get(v___y_293_, 13);
v___x_312_ = lean_st_ref_get(v___y_294_);
v_traceState_313_ = lean_ctor_get(v___x_312_, 4);
lean_inc_ref(v_traceState_313_);
lean_dec(v___x_312_);
v_traces_314_ = lean_ctor_get(v_traceState_313_, 0);
lean_inc_ref(v_traces_314_);
lean_dec_ref(v_traceState_313_);
v_ref_315_ = l_Lean_replaceRef(v_ref_291_, v_ref_301_);
lean_inc_ref(v_inheritedTraceOptions_311_);
lean_inc(v_cancelTk_x3f_309_);
lean_inc(v_currMacroScope_307_);
lean_inc(v_quotContext_306_);
lean_inc(v_maxHeartbeats_305_);
lean_inc(v_initHeartbeats_304_);
lean_inc(v_openDecls_303_);
lean_inc(v_currNamespace_302_);
lean_inc(v_maxRecDepth_300_);
lean_inc(v_currRecDepth_299_);
lean_inc_ref(v_options_298_);
lean_inc_ref(v_fileMap_297_);
lean_inc_ref(v_fileName_296_);
v___x_316_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_316_, 0, v_fileName_296_);
lean_ctor_set(v___x_316_, 1, v_fileMap_297_);
lean_ctor_set(v___x_316_, 2, v_options_298_);
lean_ctor_set(v___x_316_, 3, v_currRecDepth_299_);
lean_ctor_set(v___x_316_, 4, v_maxRecDepth_300_);
lean_ctor_set(v___x_316_, 5, v_ref_315_);
lean_ctor_set(v___x_316_, 6, v_currNamespace_302_);
lean_ctor_set(v___x_316_, 7, v_openDecls_303_);
lean_ctor_set(v___x_316_, 8, v_initHeartbeats_304_);
lean_ctor_set(v___x_316_, 9, v_maxHeartbeats_305_);
lean_ctor_set(v___x_316_, 10, v_quotContext_306_);
lean_ctor_set(v___x_316_, 11, v_currMacroScope_307_);
lean_ctor_set(v___x_316_, 12, v_cancelTk_x3f_309_);
lean_ctor_set(v___x_316_, 13, v_inheritedTraceOptions_311_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*14, v_diag_308_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*14 + 1, v_suppressElabErrors_310_);
v___x_317_ = l_Lean_PersistentArray_toArray___redArg(v_traces_314_);
lean_dec_ref(v_traces_314_);
v_sz_318_ = lean_array_size(v___x_317_);
v___x_319_ = ((size_t)0ULL);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6(v_sz_318_, v___x_319_, v___x_317_);
v_msg_321_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_321_, 0, v_data_290_);
lean_ctor_set(v_msg_321_, 1, v_msg_292_);
lean_ctor_set(v_msg_321_, 2, v___x_320_);
v___x_322_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v_msg_321_, v___x_316_, v___y_294_);
lean_dec_ref(v___x_316_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_360_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_360_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_360_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v_traceState_328_; lean_object* v_env_329_; lean_object* v_nextMacroScope_330_; lean_object* v_ngen_331_; lean_object* v_auxDeclNGen_332_; lean_object* v_cache_333_; lean_object* v_messages_334_; lean_object* v_infoState_335_; lean_object* v_snapshotTasks_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_359_; 
v___x_327_ = lean_st_ref_take(v___y_294_);
v_traceState_328_ = lean_ctor_get(v___x_327_, 4);
v_env_329_ = lean_ctor_get(v___x_327_, 0);
v_nextMacroScope_330_ = lean_ctor_get(v___x_327_, 1);
v_ngen_331_ = lean_ctor_get(v___x_327_, 2);
v_auxDeclNGen_332_ = lean_ctor_get(v___x_327_, 3);
v_cache_333_ = lean_ctor_get(v___x_327_, 5);
v_messages_334_ = lean_ctor_get(v___x_327_, 6);
v_infoState_335_ = lean_ctor_get(v___x_327_, 7);
v_snapshotTasks_336_ = lean_ctor_get(v___x_327_, 8);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_359_ == 0)
{
v___x_338_ = v___x_327_;
v_isShared_339_ = v_isSharedCheck_359_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snapshotTasks_336_);
lean_inc(v_infoState_335_);
lean_inc(v_messages_334_);
lean_inc(v_cache_333_);
lean_inc(v_traceState_328_);
lean_inc(v_auxDeclNGen_332_);
lean_inc(v_ngen_331_);
lean_inc(v_nextMacroScope_330_);
lean_inc(v_env_329_);
lean_dec(v___x_327_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_359_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint64_t v_tid_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_357_; 
v_tid_340_ = lean_ctor_get_uint64(v_traceState_328_, sizeof(void*)*1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_traceState_328_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_traceState_328_, 0);
lean_dec(v_unused_358_);
v___x_342_ = v_traceState_328_;
v_isShared_343_ = v_isSharedCheck_357_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_traceState_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_357_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_ref_291_);
lean_ctor_set(v___x_344_, 1, v_a_323_);
v___x_345_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_289_, v___x_344_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_345_);
lean_ctor_set_uint64(v_reuseFailAlloc_356_, sizeof(void*)*1, v_tid_340_);
v___x_347_ = v_reuseFailAlloc_356_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 4, v___x_347_);
v___x_349_ = v___x_338_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_env_329_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_nextMacroScope_330_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_ngen_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_auxDeclNGen_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_cache_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_messages_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_infoState_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_snapshotTasks_336_);
v___x_349_ = v_reuseFailAlloc_355_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_st_ref_set(v___y_294_, v___x_349_);
v___x_351_ = lean_box(0);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_351_);
v___x_353_ = v___x_325_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5___boxed(lean_object* v_oldTraces_361_, lean_object* v_data_362_, lean_object* v_ref_363_, lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(v_oldTraces_361_, v_data_362_, v_ref_363_, v_msg_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__0));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2(void){
_start:
{
lean_object* v___x_372_; double v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_float_of_nat(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__3));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5(void){
_start:
{
lean_object* v___x_377_; double v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(1000u);
v___x_378_ = lean_float_of_nat(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(lean_object* v_cls_379_, uint8_t v_collapsed_380_, lean_object* v_tag_381_, lean_object* v_opts_382_, uint8_t v_clsEnabled_383_, lean_object* v_oldTraces_384_, lean_object* v_msg_385_, lean_object* v_resStartStop_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_489_; 
v_fst_390_ = lean_ctor_get(v_resStartStop_386_, 0);
v_snd_391_ = lean_ctor_get(v_resStartStop_386_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_resStartStop_386_);
if (v_isSharedCheck_489_ == 0)
{
v___x_393_ = v_resStartStop_386_;
v_isShared_394_ = v_isSharedCheck_489_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snd_391_);
lean_inc(v_fst_390_);
lean_dec(v_resStartStop_386_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_489_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v_data_398_; lean_object* v_fst_409_; lean_object* v_snd_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_488_; 
v_fst_409_ = lean_ctor_get(v_snd_391_, 0);
v_snd_410_ = lean_ctor_get(v_snd_391_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_snd_391_);
if (v_isSharedCheck_488_ == 0)
{
v___x_412_ = v_snd_391_;
v_isShared_413_ = v_isSharedCheck_488_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_snd_410_);
lean_inc(v_fst_409_);
lean_dec(v_snd_391_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_488_;
goto v_resetjp_411_;
}
v___jp_395_:
{
lean_object* v___x_399_; 
lean_inc(v___y_396_);
v___x_399_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(v_oldTraces_384_, v_data_398_, v___y_396_, v___y_397_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref(v___x_399_);
v___x_400_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_fst_390_);
return v___x_400_;
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_fst_390_);
v_a_401_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___y_417_; lean_object* v_a_418_; uint8_t v___y_442_; double v___y_473_; 
v___x_414_ = l_Lean_trace_profiler;
v___x_415_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_opts_382_, v___x_414_);
if (v___x_415_ == 0)
{
v___y_442_ = v___x_415_;
goto v___jp_441_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = l_Lean_trace_profiler_useHeartbeats;
v___x_479_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_opts_382_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; double v___x_482_; double v___x_483_; double v___x_484_; 
v___x_480_ = l_Lean_trace_profiler_threshold;
v___x_481_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(v_opts_382_, v___x_480_);
v___x_482_ = lean_float_of_nat(v___x_481_);
v___x_483_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5);
v___x_484_ = lean_float_div(v___x_482_, v___x_483_);
v___y_473_ = v___x_484_;
goto v___jp_472_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; double v___x_487_; 
v___x_485_ = l_Lean_trace_profiler_threshold;
v___x_486_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(v_opts_382_, v___x_485_);
v___x_487_ = lean_float_of_nat(v___x_486_);
v___y_473_ = v___x_487_;
goto v___jp_472_;
}
}
v___jp_416_:
{
uint8_t v_result_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v_result_419_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4(v_fst_390_);
v___x_420_ = l_Lean_TraceResult_toEmoji(v_result_419_);
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
v___x_422_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 7);
lean_ctor_set(v___x_412_, 1, v___x_422_);
lean_ctor_set(v___x_412_, 0, v___x_421_);
v___x_424_ = v___x_412_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_435_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v_m_426_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 7);
lean_ctor_set(v___x_393_, 1, v_a_418_);
lean_ctor_set(v___x_393_, 0, v___x_424_);
v_m_426_ = v___x_393_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_418_);
v_m_426_ = v_reuseFailAlloc_434_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; double v___x_429_; lean_object* v_data_430_; 
v___x_427_ = lean_box(v_result_419_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___x_429_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2);
lean_inc_ref(v_tag_381_);
lean_inc_ref(v___x_428_);
lean_inc(v_cls_379_);
v_data_430_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_430_, 0, v_cls_379_);
lean_ctor_set(v_data_430_, 1, v___x_428_);
lean_ctor_set(v_data_430_, 2, v_tag_381_);
lean_ctor_set_float(v_data_430_, sizeof(void*)*3, v___x_429_);
lean_ctor_set_float(v_data_430_, sizeof(void*)*3 + 8, v___x_429_);
lean_ctor_set_uint8(v_data_430_, sizeof(void*)*3 + 16, v_collapsed_380_);
if (v___x_415_ == 0)
{
lean_dec_ref(v___x_428_);
lean_dec(v_snd_410_);
lean_dec(v_fst_409_);
lean_dec_ref(v_tag_381_);
lean_dec(v_cls_379_);
v___y_396_ = v___y_417_;
v___y_397_ = v_m_426_;
v_data_398_ = v_data_430_;
goto v___jp_395_;
}
else
{
lean_object* v_data_431_; double v___x_432_; double v___x_433_; 
lean_dec_ref(v_data_430_);
v_data_431_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_431_, 0, v_cls_379_);
lean_ctor_set(v_data_431_, 1, v___x_428_);
lean_ctor_set(v_data_431_, 2, v_tag_381_);
v___x_432_ = lean_unbox_float(v_fst_409_);
lean_dec(v_fst_409_);
lean_ctor_set_float(v_data_431_, sizeof(void*)*3, v___x_432_);
v___x_433_ = lean_unbox_float(v_snd_410_);
lean_dec(v_snd_410_);
lean_ctor_set_float(v_data_431_, sizeof(void*)*3 + 8, v___x_433_);
lean_ctor_set_uint8(v_data_431_, sizeof(void*)*3 + 16, v_collapsed_380_);
v___y_396_ = v___y_417_;
v___y_397_ = v_m_426_;
v_data_398_ = v_data_431_;
goto v___jp_395_;
}
}
}
}
v___jp_436_:
{
lean_object* v_ref_437_; lean_object* v___x_438_; 
v_ref_437_ = lean_ctor_get(v___y_387_, 5);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v_fst_390_);
v___x_438_ = lean_apply_4(v_msg_385_, v_fst_390_, v___y_387_, v___y_388_, lean_box(0));
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v___y_417_ = v_ref_437_;
v_a_418_ = v_a_439_;
goto v___jp_416_;
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4);
v___y_417_ = v_ref_437_;
v_a_418_ = v___x_440_;
goto v___jp_416_;
}
}
v___jp_441_:
{
if (v_clsEnabled_383_ == 0)
{
if (v___y_442_ == 0)
{
lean_object* v___x_443_; lean_object* v_traceState_444_; lean_object* v_env_445_; lean_object* v_nextMacroScope_446_; lean_object* v_ngen_447_; lean_object* v_auxDeclNGen_448_; lean_object* v_cache_449_; lean_object* v_messages_450_; lean_object* v_infoState_451_; lean_object* v_snapshotTasks_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_471_; 
lean_del_object(v___x_412_);
lean_dec(v_snd_410_);
lean_dec(v_fst_409_);
lean_del_object(v___x_393_);
lean_dec_ref(v_msg_385_);
lean_dec_ref(v_tag_381_);
lean_dec(v_cls_379_);
v___x_443_ = lean_st_ref_take(v___y_388_);
v_traceState_444_ = lean_ctor_get(v___x_443_, 4);
v_env_445_ = lean_ctor_get(v___x_443_, 0);
v_nextMacroScope_446_ = lean_ctor_get(v___x_443_, 1);
v_ngen_447_ = lean_ctor_get(v___x_443_, 2);
v_auxDeclNGen_448_ = lean_ctor_get(v___x_443_, 3);
v_cache_449_ = lean_ctor_get(v___x_443_, 5);
v_messages_450_ = lean_ctor_get(v___x_443_, 6);
v_infoState_451_ = lean_ctor_get(v___x_443_, 7);
v_snapshotTasks_452_ = lean_ctor_get(v___x_443_, 8);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_471_ == 0)
{
v___x_454_ = v___x_443_;
v_isShared_455_ = v_isSharedCheck_471_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_snapshotTasks_452_);
lean_inc(v_infoState_451_);
lean_inc(v_messages_450_);
lean_inc(v_cache_449_);
lean_inc(v_traceState_444_);
lean_inc(v_auxDeclNGen_448_);
lean_inc(v_ngen_447_);
lean_inc(v_nextMacroScope_446_);
lean_inc(v_env_445_);
lean_dec(v___x_443_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_471_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint64_t v_tid_456_; lean_object* v_traces_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_470_; 
v_tid_456_ = lean_ctor_get_uint64(v_traceState_444_, sizeof(void*)*1);
v_traces_457_ = lean_ctor_get(v_traceState_444_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_traceState_444_);
if (v_isSharedCheck_470_ == 0)
{
v___x_459_ = v_traceState_444_;
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_traces_457_);
lean_dec(v_traceState_444_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_384_, v_traces_457_);
lean_dec_ref(v_traces_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_461_);
lean_ctor_set_uint64(v_reuseFailAlloc_469_, sizeof(void*)*1, v_tid_456_);
v___x_463_ = v_reuseFailAlloc_469_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 4, v___x_463_);
v___x_465_ = v___x_454_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_env_445_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_nextMacroScope_446_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_ngen_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_auxDeclNGen_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_cache_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_messages_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_infoState_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_snapshotTasks_452_);
v___x_465_ = v_reuseFailAlloc_468_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_st_ref_set(v___y_388_, v___x_465_);
v___x_467_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_fst_390_);
return v___x_467_;
}
}
}
}
}
else
{
goto v___jp_436_;
}
}
else
{
goto v___jp_436_;
}
}
v___jp_472_:
{
double v___x_474_; double v___x_475_; double v___x_476_; uint8_t v___x_477_; 
v___x_474_ = lean_unbox_float(v_snd_410_);
v___x_475_ = lean_unbox_float(v_fst_409_);
v___x_476_ = lean_float_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_float_decLt(v___y_473_, v___x_476_);
v___y_442_ = v___x_477_;
goto v___jp_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___boxed(lean_object* v_cls_490_, lean_object* v_collapsed_491_, lean_object* v_tag_492_, lean_object* v_opts_493_, lean_object* v_clsEnabled_494_, lean_object* v_oldTraces_495_, lean_object* v_msg_496_, lean_object* v_resStartStop_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v_collapsed_boxed_501_; uint8_t v_clsEnabled_boxed_502_; lean_object* v_res_503_; 
v_collapsed_boxed_501_ = lean_unbox(v_collapsed_491_);
v_clsEnabled_boxed_502_ = lean_unbox(v_clsEnabled_494_);
v_res_503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v_cls_490_, v_collapsed_boxed_501_, v_tag_492_, v_opts_493_, v_clsEnabled_boxed_502_, v_oldTraces_495_, v_msg_496_, v_resStartStop_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_opts_493_);
return v_res_503_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__3(void){
_start:
{
lean_object* v___x_508_; double v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1000000000u);
v___x_509_ = lean_float_of_nat(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_options_514_; uint8_t v_hasTrace_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___y_519_; 
v_options_514_ = lean_ctor_get(v_a_511_, 2);
v_hasTrace_515_ = lean_ctor_get_uint8(v_options_514_, sizeof(void*)*1);
v___x_516_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_517_ = lean_box(0);
if (v_hasTrace_515_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_536_ = lean_st_ref_get(v___x_516_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_array_get_size(v___x_536_);
v___x_539_ = lean_nat_dec_lt(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec(v___x_536_);
lean_dec(v_name_510_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_517_);
return v___x_540_;
}
else
{
if (v___x_539_ == 0)
{
lean_object* v___x_541_; 
lean_dec(v___x_536_);
lean_dec(v_name_510_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_517_);
return v___x_541_;
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_538_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_510_, v___x_536_, v___x_542_, v___x_543_, v_a_511_, v_a_512_);
lean_dec(v___x_536_);
v___y_519_ = v___x_544_;
goto v___jp_518_;
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_651_; 
v___x_545_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_546_ = l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(v___x_545_, v_a_511_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_651_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_651_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_651_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v_a_556_; lean_object* v___y_570_; lean_object* v___y_571_; uint8_t v_a_572_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v_a_578_; lean_object* v___y_589_; lean_object* v___y_590_; uint8_t v_a_591_; uint8_t v___x_635_; 
lean_inc(v_name_510_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_551_, 0, v_name_510_);
v___x_552_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_635_ = lean_unbox(v_a_547_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_trace_profiler;
v___x_637_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_514_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
lean_dec_ref(v___f_551_);
lean_dec(v_a_547_);
v___x_638_ = lean_st_ref_get(v___x_516_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v___x_638_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_638_);
lean_dec(v_name_510_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_517_);
v___x_643_ = v___x_549_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_517_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
if (v___x_641_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v___x_638_);
lean_dec(v_name_510_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_517_);
v___x_646_ = v___x_549_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_517_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_549_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_640_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_510_, v___x_638_, v___x_648_, v___x_649_, v_a_511_, v_a_512_);
lean_dec(v___x_638_);
v___y_519_ = v___x_650_;
goto v___jp_518_;
}
}
}
else
{
lean_del_object(v___x_549_);
goto v___jp_594_;
}
}
else
{
lean_del_object(v___x_549_);
goto v___jp_594_;
}
v___jp_553_:
{
lean_object* v___x_557_; double v___x_558_; double v___x_559_; double v___x_560_; double v___x_561_; double v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___x_557_ = lean_io_mono_nanos_now();
v___x_558_ = lean_float_of_nat(v___y_554_);
v___x_559_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__3, &l_Lean_executeReservedNameAction___closed__3_once, _init_l_Lean_executeReservedNameAction___closed__3);
v___x_560_ = lean_float_div(v___x_558_, v___x_559_);
v___x_561_ = lean_float_of_nat(v___x_557_);
v___x_562_ = lean_float_div(v___x_561_, v___x_559_);
v___x_563_ = lean_box_float(v___x_560_);
v___x_564_ = lean_box_float(v___x_562_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_556_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
v___x_568_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v___x_545_, v_hasTrace_515_, v___x_552_, v_options_514_, v___x_567_, v___y_555_, v___f_551_, v___x_566_, v_a_511_, v_a_512_);
v___y_519_ = v___x_568_;
goto v___jp_518_;
}
v___jp_569_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(v_a_572_);
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___y_554_ = v___y_570_;
v___y_555_ = v___y_571_;
v_a_556_ = v___x_574_;
goto v___jp_553_;
}
v___jp_575_:
{
lean_object* v___x_579_; double v___x_580_; double v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___x_579_ = lean_io_get_num_heartbeats();
v___x_580_ = lean_float_of_nat(v___y_576_);
v___x_581_ = lean_float_of_nat(v___x_579_);
v___x_582_ = lean_box_float(v___x_580_);
v___x_583_ = lean_box_float(v___x_581_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_578_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v___x_545_, v_hasTrace_515_, v___x_552_, v_options_514_, v___x_586_, v___y_577_, v___f_551_, v___x_585_, v_a_511_, v_a_512_);
v___y_519_ = v___x_587_;
goto v___jp_518_;
}
v___jp_588_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_box(v_a_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___y_576_ = v___y_589_;
v___y_577_ = v___y_590_;
v_a_578_ = v___x_593_;
goto v___jp_575_;
}
v___jp_594_:
{
lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_595_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(v_a_512_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_595_);
v___x_597_ = l_Lean_trace_profiler_useHeartbeats;
v___x_598_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_514_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_599_ = lean_io_mono_nanos_now();
v___x_600_ = lean_st_ref_get(v___x_516_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_array_get_size(v___x_600_);
v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v___x_600_);
lean_dec(v_name_510_);
v___y_570_ = v___x_599_;
v___y_571_ = v_a_596_;
v_a_572_ = v___x_598_;
goto v___jp_569_;
}
else
{
if (v___x_603_ == 0)
{
lean_dec(v___x_600_);
lean_dec(v_name_510_);
v___y_570_ = v___x_599_;
v___y_571_ = v_a_596_;
v_a_572_ = v___x_598_;
goto v___jp_569_;
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_602_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_510_, v___x_600_, v___x_604_, v___x_605_, v_a_511_, v_a_512_);
lean_dec(v___x_600_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; uint8_t v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
v___y_570_ = v___x_599_;
v___y_571_ = v_a_596_;
v_a_572_ = v___x_608_;
goto v___jp_569_;
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_606_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_606_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 0);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v___y_554_ = v___x_599_;
v___y_555_ = v_a_596_;
v_a_556_ = v___x_614_;
goto v___jp_553_;
}
}
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_617_ = lean_io_get_num_heartbeats();
v___x_618_ = lean_st_ref_get(v___x_516_);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v___x_618_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v___x_618_);
lean_dec(v_name_510_);
v___y_589_ = v___x_617_;
v___y_590_ = v_a_596_;
v_a_591_ = v___x_621_;
goto v___jp_588_;
}
else
{
if (v___x_621_ == 0)
{
lean_dec(v___x_618_);
lean_dec(v_name_510_);
v___y_589_ = v___x_617_;
v___y_590_ = v_a_596_;
v_a_591_ = v___x_621_;
goto v___jp_588_;
}
else
{
size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((size_t)0ULL);
v___x_623_ = lean_usize_of_nat(v___x_620_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_510_, v___x_618_, v___x_622_, v___x_623_, v_a_511_, v_a_512_);
lean_dec(v___x_618_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; uint8_t v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___x_624_);
v___x_626_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
v___y_589_ = v___x_617_;
v___y_590_ = v_a_596_;
v_a_591_ = v___x_626_;
goto v___jp_588_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_624_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_624_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
v___y_576_ = v___x_617_;
v___y_577_ = v_a_596_;
v_a_578_ = v___x_632_;
goto v___jp_575_;
}
}
}
}
}
}
}
}
}
v___jp_518_:
{
if (lean_obj_tag(v___y_519_) == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_isSharedCheck_526_ = !lean_is_exclusive(v___y_519_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___y_519_, 0);
lean_dec(v_unused_527_);
v___x_521_ = v___y_519_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___y_519_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_517_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_517_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___y_519_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___y_519_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___y_519_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___y_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_executeReservedNameAction(v_name_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6(lean_object* v_00_u03b1_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_x_658_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___boxed(lean_object* v_00_u03b1_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6(v_00_u03b1_663_, v_x_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_676_, uint8_t v_suppressElabErrors_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 1)
{
lean_object* v_pre_679_; 
v_pre_679_ = lean_ctor_get(v_x_678_, 0);
switch(lean_obj_tag(v_pre_679_))
{
case 1:
{
lean_object* v_pre_680_; 
v_pre_680_ = lean_ctor_get(v_pre_679_, 0);
switch(lean_obj_tag(v_pre_680_))
{
case 0:
{
lean_object* v_str_681_; lean_object* v_str_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_str_681_ = lean_ctor_get(v_x_678_, 1);
v_str_682_ = lean_ctor_get(v_pre_679_, 1);
v___x_683_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_684_ = lean_string_dec_eq(v_str_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_686_ = lean_string_dec_eq(v_str_682_, v___x_685_);
if (v___x_686_ == 0)
{
return v___y_676_;
}
else
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_688_ = lean_string_dec_eq(v_str_681_, v___x_687_);
if (v___x_688_ == 0)
{
return v___y_676_;
}
else
{
return v_suppressElabErrors_677_;
}
}
}
else
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_690_ = lean_string_dec_eq(v_str_681_, v___x_689_);
if (v___x_690_ == 0)
{
return v___y_676_;
}
else
{
return v_suppressElabErrors_677_;
}
}
}
case 1:
{
lean_object* v_pre_691_; 
v_pre_691_ = lean_ctor_get(v_pre_680_, 0);
if (lean_obj_tag(v_pre_691_) == 0)
{
lean_object* v_str_692_; lean_object* v_str_693_; lean_object* v_str_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_str_692_ = lean_ctor_get(v_x_678_, 1);
v_str_693_ = lean_ctor_get(v_pre_679_, 1);
v_str_694_ = lean_ctor_get(v_pre_680_, 1);
v___x_695_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_696_ = lean_string_dec_eq(v_str_694_, v___x_695_);
if (v___x_696_ == 0)
{
return v___y_676_;
}
else
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_698_ = lean_string_dec_eq(v_str_693_, v___x_697_);
if (v___x_698_ == 0)
{
return v___y_676_;
}
else
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_700_ = lean_string_dec_eq(v_str_692_, v___x_699_);
if (v___x_700_ == 0)
{
return v___y_676_;
}
else
{
return v_suppressElabErrors_677_;
}
}
}
}
else
{
return v___y_676_;
}
}
default: 
{
return v___y_676_;
}
}
}
case 0:
{
lean_object* v_str_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_str_701_ = lean_ctor_get(v_x_678_, 1);
v___x_702_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0));
v___x_703_ = lean_string_dec_eq(v_str_701_, v___x_702_);
if (v___x_703_ == 0)
{
return v___y_676_;
}
else
{
return v_suppressElabErrors_677_;
}
}
default: 
{
return v___y_676_;
}
}
}
else
{
return v___y_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_704_, lean_object* v_suppressElabErrors_705_, lean_object* v_x_706_){
_start:
{
uint8_t v___y_4690__boxed_707_; uint8_t v_suppressElabErrors_boxed_708_; uint8_t v_res_709_; lean_object* v_r_710_; 
v___y_4690__boxed_707_ = lean_unbox(v___y_704_);
v_suppressElabErrors_boxed_708_ = lean_unbox(v_suppressElabErrors_705_);
v_res_709_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4690__boxed_707_, v_suppressElabErrors_boxed_708_, v_x_706_);
lean_dec(v_x_706_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_711_, lean_object* v_msgData_712_, uint8_t v_severity_713_, uint8_t v_isSilent_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_780_; lean_object* v___y_781_; uint8_t v___y_782_; lean_object* v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_797_; uint8_t v___x_802_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; uint8_t v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; uint8_t v___y_810_; uint8_t v___y_812_; uint8_t v___x_827_; 
v___x_802_ = 2;
v___x_827_ = l_Lean_instBEqMessageSeverity_beq(v_severity_713_, v___x_802_);
if (v___x_827_ == 0)
{
v___y_812_ = v___x_827_;
goto v___jp_811_;
}
else
{
uint8_t v___x_828_; 
lean_inc_ref(v_msgData_712_);
v___x_828_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_712_);
v___y_812_ = v___x_828_;
goto v___jp_811_;
}
v___jp_718_:
{
lean_object* v___x_728_; lean_object* v_currNamespace_729_; lean_object* v_openDecls_730_; lean_object* v_env_731_; lean_object* v_nextMacroScope_732_; lean_object* v_ngen_733_; lean_object* v_auxDeclNGen_734_; lean_object* v_traceState_735_; lean_object* v_cache_736_; lean_object* v_messages_737_; lean_object* v_infoState_738_; lean_object* v_snapshotTasks_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_753_; 
v___x_728_ = lean_st_ref_take(v___y_727_);
v_currNamespace_729_ = lean_ctor_get(v___y_726_, 6);
v_openDecls_730_ = lean_ctor_get(v___y_726_, 7);
v_env_731_ = lean_ctor_get(v___x_728_, 0);
v_nextMacroScope_732_ = lean_ctor_get(v___x_728_, 1);
v_ngen_733_ = lean_ctor_get(v___x_728_, 2);
v_auxDeclNGen_734_ = lean_ctor_get(v___x_728_, 3);
v_traceState_735_ = lean_ctor_get(v___x_728_, 4);
v_cache_736_ = lean_ctor_get(v___x_728_, 5);
v_messages_737_ = lean_ctor_get(v___x_728_, 6);
v_infoState_738_ = lean_ctor_get(v___x_728_, 7);
v_snapshotTasks_739_ = lean_ctor_get(v___x_728_, 8);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_753_ == 0)
{
v___x_741_ = v___x_728_;
v_isShared_742_ = v_isSharedCheck_753_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snapshotTasks_739_);
lean_inc(v_infoState_738_);
lean_inc(v_messages_737_);
lean_inc(v_cache_736_);
lean_inc(v_traceState_735_);
lean_inc(v_auxDeclNGen_734_);
lean_inc(v_ngen_733_);
lean_inc(v_nextMacroScope_732_);
lean_inc(v_env_731_);
lean_dec(v___x_728_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_753_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_inc(v_openDecls_730_);
lean_inc(v_currNamespace_729_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_currNamespace_729_);
lean_ctor_set(v___x_743_, 1, v_openDecls_730_);
v___x_744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___y_723_);
lean_inc_ref(v___y_724_);
v___x_745_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_745_, 0, v___y_724_);
lean_ctor_set(v___x_745_, 1, v___y_722_);
lean_ctor_set(v___x_745_, 2, v___y_721_);
lean_ctor_set(v___x_745_, 3, v___y_720_);
lean_ctor_set(v___x_745_, 4, v___x_744_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5, v___y_719_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5 + 1, v___y_725_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5 + 2, v_isSilent_714_);
v___x_746_ = l_Lean_MessageLog_add(v___x_745_, v_messages_737_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 6, v___x_746_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_env_731_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_nextMacroScope_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_ngen_733_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_auxDeclNGen_734_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_traceState_735_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_cache_736_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v_infoState_738_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_snapshotTasks_739_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_st_ref_set(v___y_727_, v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
v___jp_754_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_778_; 
v___x_763_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_712_);
v___x_764_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v___x_763_, v___y_715_, v___y_716_);
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_778_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_inc_ref(v___y_757_);
v___x_769_ = l_Lean_FileMap_toPosition(v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_inc_ref(v___y_757_);
v___x_770_ = l_Lean_FileMap_toPosition(v___y_757_, v___y_762_);
lean_dec(v___y_762_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_759_ == 0)
{
lean_del_object(v___x_767_);
lean_dec_ref(v___y_755_);
v___y_719_ = v___y_756_;
v___y_720_ = v___x_772_;
v___y_721_ = v___x_771_;
v___y_722_ = v___x_769_;
v___y_723_ = v_a_765_;
v___y_724_ = v___y_760_;
v___y_725_ = v___y_761_;
v___y_726_ = v___y_715_;
v___y_727_ = v___y_716_;
goto v___jp_718_;
}
else
{
uint8_t v___x_773_; 
lean_inc(v_a_765_);
v___x_773_ = l_Lean_MessageData_hasTag(v___y_755_, v_a_765_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec_ref(v___x_771_);
lean_dec_ref(v___x_769_);
lean_dec(v_a_765_);
v___x_774_ = lean_box(0);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_774_);
v___x_776_ = v___x_767_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_del_object(v___x_767_);
v___y_719_ = v___y_756_;
v___y_720_ = v___x_772_;
v___y_721_ = v___x_771_;
v___y_722_ = v___x_769_;
v___y_723_ = v_a_765_;
v___y_724_ = v___y_760_;
v___y_725_ = v___y_761_;
v___y_726_ = v___y_715_;
v___y_727_ = v___y_716_;
goto v___jp_718_;
}
}
}
}
v___jp_779_:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Syntax_getTailPos_x3f(v___y_783_, v___y_782_);
lean_dec(v___y_783_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_inc(v___y_787_);
v___y_755_ = v___y_780_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_787_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_786_;
v___y_762_ = v___y_787_;
goto v___jp_754_;
}
else
{
lean_object* v_val_789_; 
v_val_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_789_);
lean_dec_ref(v___x_788_);
v___y_755_ = v___y_780_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_787_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_786_;
v___y_762_ = v_val_789_;
goto v___jp_754_;
}
}
v___jp_790_:
{
lean_object* v_ref_798_; lean_object* v___x_799_; 
v_ref_798_ = l_Lean_replaceRef(v_ref_711_, v___y_795_);
v___x_799_ = l_Lean_Syntax_getPos_x3f(v_ref_798_, v___y_792_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___y_780_ = v___y_791_;
v___y_781_ = v___y_793_;
v___y_782_ = v___y_792_;
v___y_783_ = v_ref_798_;
v___y_784_ = v___y_794_;
v___y_785_ = v___y_796_;
v___y_786_ = v___y_797_;
v___y_787_ = v___x_800_;
goto v___jp_779_;
}
else
{
lean_object* v_val_801_; 
v_val_801_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_801_);
lean_dec_ref(v___x_799_);
v___y_780_ = v___y_791_;
v___y_781_ = v___y_793_;
v___y_782_ = v___y_792_;
v___y_783_ = v_ref_798_;
v___y_784_ = v___y_794_;
v___y_785_ = v___y_796_;
v___y_786_ = v___y_797_;
v___y_787_ = v_val_801_;
goto v___jp_779_;
}
}
v___jp_803_:
{
if (v___y_810_ == 0)
{
v___y_791_ = v___y_805_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_804_;
v___y_794_ = v___y_807_;
v___y_795_ = v___y_806_;
v___y_796_ = v___y_808_;
v___y_797_ = v_severity_713_;
goto v___jp_790_;
}
else
{
v___y_791_ = v___y_805_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_804_;
v___y_794_ = v___y_807_;
v___y_795_ = v___y_806_;
v___y_796_ = v___y_808_;
v___y_797_ = v___x_802_;
goto v___jp_790_;
}
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
lean_object* v_fileName_813_; lean_object* v_fileMap_814_; lean_object* v_options_815_; lean_object* v_ref_816_; uint8_t v_suppressElabErrors_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; uint8_t v___x_821_; uint8_t v___x_822_; 
v_fileName_813_ = lean_ctor_get(v___y_715_, 0);
v_fileMap_814_ = lean_ctor_get(v___y_715_, 1);
v_options_815_ = lean_ctor_get(v___y_715_, 2);
v_ref_816_ = lean_ctor_get(v___y_715_, 5);
v_suppressElabErrors_817_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*14 + 1);
v___x_818_ = lean_box(v___y_812_);
v___x_819_ = lean_box(v_suppressElabErrors_817_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_820_, 0, v___x_818_);
lean_closure_set(v___f_820_, 1, v___x_819_);
v___x_821_ = 1;
v___x_822_ = l_Lean_instBEqMessageSeverity_beq(v_severity_713_, v___x_821_);
if (v___x_822_ == 0)
{
v___y_804_ = v_fileMap_814_;
v___y_805_ = v___f_820_;
v___y_806_ = v_ref_816_;
v___y_807_ = v_suppressElabErrors_817_;
v___y_808_ = v_fileName_813_;
v___y_809_ = v___y_812_;
v___y_810_ = v___x_822_;
goto v___jp_803_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = l_Lean_warningAsError;
v___x_824_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_815_, v___x_823_);
v___y_804_ = v_fileMap_814_;
v___y_805_ = v___f_820_;
v___y_806_ = v_ref_816_;
v___y_807_ = v_suppressElabErrors_817_;
v___y_808_ = v_fileName_813_;
v___y_809_ = v___y_812_;
v___y_810_ = v___x_824_;
goto v___jp_803_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_msgData_712_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_829_, lean_object* v_msgData_830_, lean_object* v_severity_831_, lean_object* v_isSilent_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_severity_boxed_836_; uint8_t v_isSilent_boxed_837_; lean_object* v_res_838_; 
v_severity_boxed_836_ = lean_unbox(v_severity_831_);
v_isSilent_boxed_837_ = lean_unbox(v_isSilent_832_);
v_res_838_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_829_, v_msgData_830_, v_severity_boxed_836_, v_isSilent_boxed_837_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v_ref_829_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_839_, uint8_t v_severity_840_, uint8_t v_isSilent_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_ref_845_; lean_object* v___x_846_; 
v_ref_845_ = lean_ctor_get(v___y_842_, 5);
v___x_846_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_845_, v_msgData_839_, v_severity_840_, v_isSilent_841_, v___y_842_, v___y_843_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_847_, lean_object* v_severity_848_, lean_object* v_isSilent_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_severity_boxed_853_; uint8_t v_isSilent_boxed_854_; lean_object* v_res_855_; 
v_severity_boxed_853_ = lean_unbox(v_severity_848_);
v_isSilent_boxed_854_ = lean_unbox(v_isSilent_849_);
v_res_855_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_847_, v_severity_boxed_853_, v_isSilent_boxed_854_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = 2;
v___x_861_ = 0;
v___x_862_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_856_, v___x_860_, v___x_861_, v___y_857_, v___y_858_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_867_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_object* v___x_880_; 
lean_dec(v_id_874_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_x_876_);
return v___x_880_;
}
else
{
lean_object* v_head_881_; lean_object* v_tail_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_939_; 
v_head_881_ = lean_ctor_get(v_x_875_, 0);
v_tail_882_ = lean_ctor_get(v_x_875_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_939_ == 0)
{
v___x_884_ = v_x_875_;
v_isShared_885_ = v_isSharedCheck_939_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_tail_882_);
lean_inc(v_head_881_);
lean_dec(v_x_875_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_939_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_fst_891_; lean_object* v___x_892_; lean_object* v_env_893_; uint8_t v___x_894_; uint8_t v___x_895_; 
v_fst_891_ = lean_ctor_get(v_head_881_, 0);
v___x_892_ = lean_st_ref_get(v___y_878_);
v_env_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_892_);
v___x_894_ = 1;
lean_inc(v_fst_891_);
v___x_895_ = l_Lean_Environment_contains(v_env_893_, v_fst_891_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_inc(v_fst_891_);
v___x_896_ = l_Lean_executeReservedNameAction(v_fst_891_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; lean_object* v_env_898_; uint8_t v___x_899_; 
lean_dec_ref(v___x_896_);
v___x_897_ = lean_st_ref_get(v___y_878_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_env_898_);
lean_dec(v___x_897_);
v___x_899_ = l_Lean_Environment_containsOnBranch(v_env_898_, v_fst_891_);
if (v___x_899_ == 0)
{
lean_del_object(v___x_884_);
lean_dec(v_head_881_);
v_x_875_ = v_tail_882_;
goto _start;
}
else
{
goto v___jp_886_;
}
}
else
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_884_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_head_881_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_937_ = lean_ctor_get(v_head_881_, 1);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_head_881_, 0);
lean_dec(v_unused_938_);
v___x_902_ = v_head_881_;
v_isShared_903_ = v_isSharedCheck_936_;
goto v_resetjp_901_;
}
else
{
lean_dec(v_head_881_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_936_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_935_; 
v_a_904_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_935_ == 0)
{
v___x_906_ = v___x_896_;
v_isShared_907_ = v_isSharedCheck_935_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_896_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_935_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___y_909_; uint8_t v___x_933_; 
v___x_933_ = l_Lean_Exception_isInterrupt(v_a_904_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; 
lean_inc(v_a_904_);
v___x_934_ = l_Lean_Exception_isRuntime(v_a_904_);
v___y_909_ = v___x_934_;
goto v___jp_908_;
}
else
{
v___y_909_ = v___x_933_;
goto v___jp_908_;
}
v___jp_908_:
{
if (v___y_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
lean_del_object(v___x_906_);
v___x_910_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_874_);
v___x_911_ = l_Lean_MessageData_ofName(v_id_874_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 7);
lean_ctor_set(v___x_902_, 1, v___x_911_);
lean_ctor_set(v___x_902_, 0, v___x_910_);
v___x_913_ = v___x_902_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_929_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_914_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_Exception_toMessageData(v_a_904_);
v___x_917_ = l_Lean_indentD(v___x_916_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_915_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_918_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref(v___x_919_);
v_x_875_ = v_tail_882_;
goto _start;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_tail_882_);
lean_dec(v_x_876_);
lean_dec(v_id_874_);
v_a_921_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_919_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
else
{
lean_object* v___x_931_; 
lean_del_object(v___x_902_);
lean_dec(v_tail_882_);
lean_dec(v_x_876_);
lean_dec(v_id_874_);
if (v_isShared_907_ == 0)
{
v___x_931_ = v___x_906_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_904_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
}
else
{
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_888_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v_x_876_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_head_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_x_876_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_x_875_ = v_tail_882_;
v_x_876_ = v___x_888_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_940_, v_x_941_, v_x_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(lean_object* v_msgData_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = 1;
v___x_952_ = 0;
v___x_953_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_947_, v___x_951_, v___x_952_, v___y_948_, v___y_949_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v_msgData_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(lean_object* v_opt_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_options_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_options_962_ = lean_ctor_get(v___y_960_, 2);
v___x_963_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_962_, v_opt_959_);
v___x_964_ = lean_box(v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_opt_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_966_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_dec_ref(v_opt_966_);
return v_res_969_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_id_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v_env_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1003_; 
v___x_980_ = lean_st_ref_get(v___y_978_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_980_);
v___x_982_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_983_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v___x_982_, v___y_977_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1003_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1003_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v_isExporting_993_; 
v_isExporting_993_ = lean_ctor_get_uint8(v_env_981_, sizeof(void*)*8);
lean_dec_ref(v_env_981_);
if (v_isExporting_993_ == 0)
{
lean_dec(v_a_984_);
lean_dec(v_id_976_);
goto v___jp_988_;
}
else
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_isPrivateName(v_id_976_);
if (v___x_994_ == 0)
{
lean_dec(v_a_984_);
lean_dec(v_id_976_);
goto v___jp_988_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_unbox(v_a_984_);
lean_dec(v_a_984_);
if (v___x_995_ == 0)
{
lean_dec(v_id_976_);
goto v___jp_988_;
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_986_);
v___x_996_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1);
v___x_997_ = 0;
v___x_998_ = l_Lean_MessageData_ofConstName(v_id_976_, v___x_997_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v___x_1001_, v___y_977_, v___y_978_);
return v___x_1002_;
}
}
}
v___jp_988_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_id_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_id_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(lean_object* v_x_1009_){
_start:
{
lean_object* v_fst_1010_; uint8_t v___x_1011_; 
v_fst_1010_ = lean_ctor_get(v_x_1009_, 0);
v___x_1011_ = l_Lean_isPrivateName(v_fst_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0___boxed(lean_object* v_x_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(v_x_1012_);
lean_dec_ref(v_x_1012_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_1016_, uint8_t v_enableLog_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_env_1022_; lean_object* v_options_1023_; lean_object* v_currNamespace_1024_; lean_object* v_openDecls_1025_; lean_object* v___x_1026_; lean_object* v_env_1027_; lean_object* v_res_1028_; 
v___x_1021_ = lean_st_ref_get(v___y_1019_);
v_env_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1022_);
lean_dec(v___x_1021_);
v_options_1023_ = lean_ctor_get(v___y_1018_, 2);
v_currNamespace_1024_ = lean_ctor_get(v___y_1018_, 6);
v_openDecls_1025_ = lean_ctor_get(v___y_1018_, 7);
v___x_1026_ = lean_st_ref_get(v___y_1019_);
v_env_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc_ref(v_env_1027_);
lean_dec(v___x_1026_);
lean_inc(v_openDecls_1025_);
lean_inc(v_currNamespace_1024_);
v_res_1028_ = l_Lean_ResolveName_resolveGlobalName(v_env_1022_, v_options_1023_, v_currNamespace_1024_, v_openDecls_1025_, v_id_1016_);
if (v_enableLog_1017_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v_env_1027_);
lean_dec_ref(v___y_1018_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_res_1028_);
return v___x_1029_;
}
else
{
uint8_t v_isExporting_1030_; 
v_isExporting_1030_ = lean_ctor_get_uint8(v_env_1027_, sizeof(void*)*8);
lean_dec_ref(v_env_1027_);
if (v_isExporting_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref(v___y_1018_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_res_1028_);
return v___x_1031_;
}
else
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0));
lean_inc(v_res_1028_);
v___x_1033_ = l_List_find_x3f___redArg(v___f_1032_, v_res_1028_);
if (lean_obj_tag(v___x_1033_) == 1)
{
lean_object* v_val_1034_; lean_object* v_fst_1035_; lean_object* v___x_1036_; 
v_val_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1034_);
lean_dec_ref(v___x_1033_);
v_fst_1035_ = lean_ctor_get(v_val_1034_, 0);
lean_inc(v_fst_1035_);
lean_dec(v_val_1034_);
v___x_1036_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_fst_1035_, v___y_1018_, v___y_1019_);
lean_dec_ref(v___y_1018_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1044_);
v___x_1038_ = v___x_1036_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_dec(v___x_1036_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_res_1028_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_res_1028_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_res_1028_);
v_a_1045_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1036_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1036_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v___x_1053_; 
lean_dec(v___x_1033_);
lean_dec_ref(v___y_1018_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_res_1028_);
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_1054_, lean_object* v_enableLog_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_enableLog_boxed_1059_; lean_object* v_res_1060_; 
v_enableLog_boxed_1059_ = lean_unbox(v_enableLog_1055_);
v_res_1060_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1054_, v_enableLog_boxed_1059_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
uint8_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = 1;
lean_inc_ref(v_a_1062_);
lean_inc(v_id_1061_);
v___x_1066_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1061_, v___x_1065_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = lean_box(0);
v___x_1069_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1061_, v_a_1067_, v___x_1068_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_List_reverse___redArg(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
return v___x_1069_;
}
}
else
{
lean_dec(v_id_1061_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_realizeGlobalName(v_id_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(lean_object* v_opt_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_1084_, v___y_1085_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___boxed(lean_object* v_opt_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(v_opt_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_opt_1089_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
if (lean_obj_tag(v_a_1094_) == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_List_reverse___redArg(v_a_1095_);
return v___x_1096_;
}
else
{
lean_object* v_head_1097_; lean_object* v_tail_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v_head_1097_ = lean_ctor_get(v_a_1094_, 0);
v_tail_1098_ = lean_ctor_get(v_a_1094_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v_a_1094_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_tail_1098_);
lean_inc(v_head_1097_);
lean_dec(v_a_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_fst_1102_; lean_object* v___x_1104_; 
v_fst_1102_ = lean_ctor_get(v_head_1097_, 0);
lean_inc(v_fst_1102_);
lean_dec(v_head_1097_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v_a_1095_);
lean_ctor_set(v___x_1100_, 0, v_fst_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_fst_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_1095_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v_a_1094_ = v_tail_1098_;
v_a_1095_ = v___x_1104_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v_ref_1112_ = lean_ctor_get(v___y_1109_, 5);
v___x_1113_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v_msg_1108_, v___y_1109_, v___y_1110_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_inc(v_ref_1112_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_ref_1112_);
lean_ctor_set(v___x_1118_, 1, v_a_1114_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 1);
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1128_, lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_fileName_1133_; lean_object* v_fileMap_1134_; lean_object* v_options_1135_; lean_object* v_currRecDepth_1136_; lean_object* v_maxRecDepth_1137_; lean_object* v_ref_1138_; lean_object* v_currNamespace_1139_; lean_object* v_openDecls_1140_; lean_object* v_initHeartbeats_1141_; lean_object* v_maxHeartbeats_1142_; lean_object* v_quotContext_1143_; lean_object* v_currMacroScope_1144_; uint8_t v_diag_1145_; lean_object* v_cancelTk_x3f_1146_; uint8_t v_suppressElabErrors_1147_; lean_object* v_inheritedTraceOptions_1148_; lean_object* v_ref_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_fileName_1133_ = lean_ctor_get(v___y_1130_, 0);
v_fileMap_1134_ = lean_ctor_get(v___y_1130_, 1);
v_options_1135_ = lean_ctor_get(v___y_1130_, 2);
v_currRecDepth_1136_ = lean_ctor_get(v___y_1130_, 3);
v_maxRecDepth_1137_ = lean_ctor_get(v___y_1130_, 4);
v_ref_1138_ = lean_ctor_get(v___y_1130_, 5);
v_currNamespace_1139_ = lean_ctor_get(v___y_1130_, 6);
v_openDecls_1140_ = lean_ctor_get(v___y_1130_, 7);
v_initHeartbeats_1141_ = lean_ctor_get(v___y_1130_, 8);
v_maxHeartbeats_1142_ = lean_ctor_get(v___y_1130_, 9);
v_quotContext_1143_ = lean_ctor_get(v___y_1130_, 10);
v_currMacroScope_1144_ = lean_ctor_get(v___y_1130_, 11);
v_diag_1145_ = lean_ctor_get_uint8(v___y_1130_, sizeof(void*)*14);
v_cancelTk_x3f_1146_ = lean_ctor_get(v___y_1130_, 12);
v_suppressElabErrors_1147_ = lean_ctor_get_uint8(v___y_1130_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1148_ = lean_ctor_get(v___y_1130_, 13);
v_ref_1149_ = l_Lean_replaceRef(v_ref_1128_, v_ref_1138_);
lean_inc_ref(v_inheritedTraceOptions_1148_);
lean_inc(v_cancelTk_x3f_1146_);
lean_inc(v_currMacroScope_1144_);
lean_inc(v_quotContext_1143_);
lean_inc(v_maxHeartbeats_1142_);
lean_inc(v_initHeartbeats_1141_);
lean_inc(v_openDecls_1140_);
lean_inc(v_currNamespace_1139_);
lean_inc(v_maxRecDepth_1137_);
lean_inc(v_currRecDepth_1136_);
lean_inc_ref(v_options_1135_);
lean_inc_ref(v_fileMap_1134_);
lean_inc_ref(v_fileName_1133_);
v___x_1150_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1150_, 0, v_fileName_1133_);
lean_ctor_set(v___x_1150_, 1, v_fileMap_1134_);
lean_ctor_set(v___x_1150_, 2, v_options_1135_);
lean_ctor_set(v___x_1150_, 3, v_currRecDepth_1136_);
lean_ctor_set(v___x_1150_, 4, v_maxRecDepth_1137_);
lean_ctor_set(v___x_1150_, 5, v_ref_1149_);
lean_ctor_set(v___x_1150_, 6, v_currNamespace_1139_);
lean_ctor_set(v___x_1150_, 7, v_openDecls_1140_);
lean_ctor_set(v___x_1150_, 8, v_initHeartbeats_1141_);
lean_ctor_set(v___x_1150_, 9, v_maxHeartbeats_1142_);
lean_ctor_set(v___x_1150_, 10, v_quotContext_1143_);
lean_ctor_set(v___x_1150_, 11, v_currMacroScope_1144_);
lean_ctor_set(v___x_1150_, 12, v_cancelTk_x3f_1146_);
lean_ctor_set(v___x_1150_, 13, v_inheritedTraceOptions_1148_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*14, v_diag_1145_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*14 + 1, v_suppressElabErrors_1147_);
v___x_1151_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1129_, v___x_1150_, v___y_1131_);
lean_dec_ref(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1152_, v_msg_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_ref_1152_);
return v_res_1157_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1169_ = l_Lean_stringToMessageData(v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1179_, lean_object* v_declHint_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; uint8_t v___x_1185_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_env_1184_);
lean_dec(v___x_1183_);
v___x_1185_ = l_Lean_Name_isAnonymous(v_declHint_1180_);
if (v___x_1185_ == 0)
{
uint8_t v_isExporting_1186_; 
v_isExporting_1186_ = lean_ctor_get_uint8(v_env_1184_, sizeof(void*)*8);
if (v_isExporting_1186_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_env_1184_);
lean_dec(v_declHint_1180_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_msg_1179_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
lean_inc_ref(v_env_1184_);
v___x_1188_ = l_Lean_Environment_setExporting(v_env_1184_, v___x_1185_);
lean_inc(v_declHint_1180_);
lean_inc_ref(v___x_1188_);
v___x_1189_ = l_Lean_Environment_contains(v___x_1188_, v_declHint_1180_, v_isExporting_1186_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v___x_1188_);
lean_dec_ref(v_env_1184_);
lean_dec(v_declHint_1180_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_msg_1179_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_c_1196_; lean_object* v___x_1197_; 
v___x_1191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2);
v___x_1192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5);
v___x_1193_ = l_Lean_Options_empty;
v___x_1194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v___x_1191_);
lean_ctor_set(v___x_1194_, 2, v___x_1192_);
lean_ctor_set(v___x_1194_, 3, v___x_1193_);
lean_inc(v_declHint_1180_);
v___x_1195_ = l_Lean_MessageData_ofConstName(v_declHint_1180_, v___x_1185_);
v_c_1196_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1196_, 0, v___x_1194_);
lean_ctor_set(v_c_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1184_, v_declHint_1180_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_env_1184_);
lean_dec(v_declHint_1180_);
v___x_1198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_c_1196_);
v___x_1200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_MessageData_note(v___x_1201_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_msg_1179_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1240_; 
v_val_1205_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1207_ = v___x_1197_;
v_isShared_1208_ = v_isSharedCheck_1240_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v___x_1197_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1240_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_mod_1212_; uint8_t v___x_1213_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Lean_Environment_header(v_env_1184_);
lean_dec_ref(v_env_1184_);
v___x_1211_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1210_);
v_mod_1212_ = lean_array_get(v___x_1209_, v___x_1211_, v_val_1205_);
lean_dec(v_val_1205_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = l_Lean_isPrivateName(v_declHint_1180_);
lean_dec(v_declHint_1180_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v_c_1196_);
v___x_1216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_MessageData_ofName(v_mod_1212_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_MessageData_note(v___x_1221_);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_msg_1179_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1223_);
v___x_1225_ = v___x_1207_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_c_1196_);
v___x_1229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = l_Lean_MessageData_ofName(v_mod_1212_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_MessageData_note(v___x_1234_);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_msg_1179_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1236_);
v___x_1238_ = v___x_1207_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1241_; 
lean_dec_ref(v_env_1184_);
lean_dec(v_declHint_1180_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_msg_1179_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1242_, lean_object* v_declHint_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1242_, v_declHint_1243_, v___y_1244_);
lean_dec(v___y_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1247_, lean_object* v_declHint_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1262_; 
v___x_1252_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1247_, v_declHint_1248_, v___y_1250_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1257_ = l_Lean_unknownIdentifierMessageTag;
v___x_1258_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1258_);
v___x_1260_ = v___x_1255_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1263_, lean_object* v_declHint_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1263_, v_declHint_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1269_, lean_object* v_msg_1270_, lean_object* v_declHint_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v_a_1276_; lean_object* v___x_1277_; 
v___x_1275_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1270_, v_declHint_1271_, v___y_1272_, v___y_1273_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1269_, v_a_1276_, v___y_1272_, v___y_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1278_, lean_object* v_msg_1279_, lean_object* v_declHint_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1278_, v_msg_1279_, v_declHint_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v_ref_1278_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1291_, lean_object* v_constName_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1296_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1297_ = 0;
lean_inc(v_constName_1292_);
v___x_1298_ = l_Lean_MessageData_ofConstName(v_constName_1292_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1296_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1291_, v___x_1301_, v_constName_1292_, v___y_1293_, v___y_1294_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1303_, lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1303_, v_constName_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v_ref_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
if (lean_obj_tag(v_a_1309_) == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = l_List_reverse___redArg(v_a_1310_);
return v___x_1311_;
}
else
{
lean_object* v_head_1312_; lean_object* v_tail_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1324_; 
v_head_1312_ = lean_ctor_get(v_a_1309_, 0);
v_tail_1313_ = lean_ctor_get(v_a_1309_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1315_ = v_a_1309_;
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_tail_1313_);
lean_inc(v_head_1312_);
lean_dec(v_a_1309_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_snd_1317_; uint8_t v___x_1318_; 
v_snd_1317_ = lean_ctor_get(v_head_1312_, 1);
v___x_1318_ = l_List_isEmpty___redArg(v_snd_1317_);
if (v___x_1318_ == 0)
{
lean_del_object(v___x_1315_);
lean_dec(v_head_1312_);
v_a_1309_ = v_tail_1313_;
goto _start;
}
else
{
lean_object* v___x_1321_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v_a_1310_);
v___x_1321_ = v___x_1315_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_head_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_a_1310_);
v___x_1321_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v_a_1309_ = v_tail_1313_;
v_a_1310_ = v___x_1321_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1325_, lean_object* v_cs_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_cs_1331_; uint8_t v___x_1335_; 
v___x_1330_ = lean_box(0);
v_cs_1331_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1326_, v___x_1330_);
v___x_1335_ = l_List_isEmpty___redArg(v_cs_1331_);
if (v___x_1335_ == 0)
{
lean_dec(v_n_1325_);
goto v___jp_1332_;
}
else
{
lean_object* v_ref_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_cs_1331_);
v_ref_1336_ = lean_ctor_get(v___y_1327_, 5);
v___x_1337_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1336_, v_n_1325_, v___y_1327_, v___y_1328_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
v___jp_1332_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1331_, v___x_1330_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1346_, lean_object* v_cs_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1346_, v_cs_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
lean_inc(v_n_1352_);
v___x_1356_ = l_Lean_realizeGlobalName(v_n_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1352_, v_a_1357_, v_a_1353_, v_a_1354_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_n_1352_);
v_a_1359_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1356_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1356_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_realizeGlobalConstCore(v_n_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1372_, lean_object* v_ref_1373_, lean_object* v_constName_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1373_, v_constName_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_ref_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1379_, v_ref_1380_, v_constName_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v_ref_1380_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1386_, lean_object* v_ref_1387_, lean_object* v_msg_1388_, lean_object* v_declHint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1387_, v_msg_1388_, v_declHint_1389_, v___y_1390_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_ref_1395_, lean_object* v_msg_1396_, lean_object* v_declHint_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1394_, v_ref_1395_, v_msg_1396_, v_declHint_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_ref_1395_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1402_, lean_object* v_declHint_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1402_, v_declHint_1403_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1408_, v_declHint_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1414_, lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1415_, v_msg_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1421_, v_ref_1422_, v_msg_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v_ref_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1428_, lean_object* v_msg_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1434_, v_msg_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = l_List_reverse___redArg(v_a_1441_);
return v___x_1442_;
}
else
{
lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1453_; 
v_head_1443_ = lean_ctor_get(v_a_1440_, 0);
v_tail_1444_ = lean_ctor_get(v_a_1440_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_a_1440_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1446_ = v_a_1440_;
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_tail_1444_);
lean_inc(v_head_1443_);
lean_dec(v_a_1440_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = l_Lean_MessageData_ofExpr(v_head_1443_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v_a_1441_);
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1441_);
v___x_1450_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
v_a_1440_ = v_tail_1444_;
v_a_1441_ = v___x_1450_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
if (lean_obj_tag(v_a_1454_) == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = l_List_reverse___redArg(v_a_1455_);
return v___x_1456_;
}
else
{
lean_object* v_head_1457_; lean_object* v_tail_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_head_1457_ = lean_ctor_get(v_a_1454_, 0);
v_tail_1458_ = lean_ctor_get(v_a_1454_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_a_1454_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v_a_1454_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_tail_1458_);
lean_inc(v_head_1457_);
lean_dec(v_a_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Lean_mkConst(v_head_1457_, v___x_1462_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_a_1455_);
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_a_1455_);
v___x_1465_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
v_a_1454_ = v_tail_1458_;
v_a_1455_ = v___x_1465_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1475_, lean_object* v_cs_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
if (lean_obj_tag(v_cs_1476_) == 1)
{
lean_object* v_tail_1492_; 
v_tail_1492_ = lean_ctor_get(v_cs_1476_, 1);
if (lean_obj_tag(v_tail_1492_) == 0)
{
lean_object* v_head_1493_; lean_object* v___x_1494_; 
lean_dec(v_n_1475_);
v_head_1493_ = lean_ctor_get(v_cs_1476_, 0);
lean_inc(v_head_1493_);
lean_dec_ref(v_cs_1476_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_head_1493_);
return v___x_1494_;
}
else
{
goto v___jp_1480_;
}
}
else
{
goto v___jp_1480_;
}
v___jp_1480_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1481_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1482_ = l_Lean_MessageData_ofName(v_n_1475_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1476_, v___x_1486_);
v___x_1488_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1487_, v___x_1486_);
v___x_1489_ = l_Lean_MessageData_ofList(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1485_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1490_, v___y_1477_, v___y_1478_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1495_, lean_object* v_cs_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1495_, v_cs_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1505_; 
lean_inc(v_n_1501_);
v___x_1505_ = l_Lean_realizeGlobalConstCore(v_n_1501_, v_a_1502_, v_a_1503_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1501_, v_a_1506_, v_a_1502_, v_a_1503_);
return v___x_1507_;
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_n_1501_);
v_a_1508_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1505_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1505_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
if (lean_obj_tag(v_a_1521_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_array_to_list(v_a_1522_);
return v___x_1523_;
}
else
{
lean_object* v_head_1524_; 
v_head_1524_ = lean_ctor_get(v_a_1521_, 0);
if (lean_obj_tag(v_head_1524_) == 1)
{
lean_object* v_fields_1525_; 
v_fields_1525_ = lean_ctor_get(v_head_1524_, 1);
if (lean_obj_tag(v_fields_1525_) == 0)
{
lean_object* v_tail_1526_; lean_object* v_n_1527_; lean_object* v___x_1528_; 
lean_inc_ref(v_head_1524_);
v_tail_1526_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_tail_1526_);
lean_dec_ref(v_a_1521_);
v_n_1527_ = lean_ctor_get(v_head_1524_, 0);
lean_inc(v_n_1527_);
lean_dec_ref(v_head_1524_);
v___x_1528_ = lean_array_push(v_a_1522_, v_n_1527_);
v_a_1521_ = v_tail_1526_;
v_a_1522_ = v___x_1528_;
goto _start;
}
else
{
lean_object* v_tail_1530_; 
v_tail_1530_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_tail_1530_);
lean_dec_ref(v_a_1521_);
v_a_1521_ = v_tail_1530_;
goto _start;
}
}
else
{
lean_object* v_tail_1532_; 
v_tail_1532_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_tail_1532_);
lean_dec_ref(v_a_1521_);
v_a_1521_ = v_tail_1532_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1540_ = l_Lean_MessageData_ofFormat(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1541_, lean_object* v_k_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (lean_obj_tag(v_stx_1541_) == 3)
{
lean_object* v_val_1546_; lean_object* v_preresolved_1547_; lean_object* v___x_1548_; lean_object* v_pre_1549_; uint8_t v___x_1550_; 
v_val_1546_ = lean_ctor_get(v_stx_1541_, 2);
lean_inc(v_val_1546_);
v_preresolved_1547_ = lean_ctor_get(v_stx_1541_, 3);
v___x_1548_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1547_);
v_pre_1549_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1547_, v___x_1548_);
v___x_1550_ = l_List_isEmpty___redArg(v_pre_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_val_1546_);
lean_dec_ref(v_stx_1541_);
lean_dec_ref(v_k_1542_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_pre_1549_);
return v___x_1551_;
}
else
{
lean_object* v_fileName_1552_; lean_object* v_fileMap_1553_; lean_object* v_options_1554_; lean_object* v_currRecDepth_1555_; lean_object* v_maxRecDepth_1556_; lean_object* v_ref_1557_; lean_object* v_currNamespace_1558_; lean_object* v_openDecls_1559_; lean_object* v_initHeartbeats_1560_; lean_object* v_maxHeartbeats_1561_; lean_object* v_quotContext_1562_; lean_object* v_currMacroScope_1563_; uint8_t v_diag_1564_; lean_object* v_cancelTk_x3f_1565_; uint8_t v_suppressElabErrors_1566_; lean_object* v_inheritedTraceOptions_1567_; lean_object* v_ref_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec(v_pre_1549_);
v_fileName_1552_ = lean_ctor_get(v___y_1543_, 0);
v_fileMap_1553_ = lean_ctor_get(v___y_1543_, 1);
v_options_1554_ = lean_ctor_get(v___y_1543_, 2);
v_currRecDepth_1555_ = lean_ctor_get(v___y_1543_, 3);
v_maxRecDepth_1556_ = lean_ctor_get(v___y_1543_, 4);
v_ref_1557_ = lean_ctor_get(v___y_1543_, 5);
v_currNamespace_1558_ = lean_ctor_get(v___y_1543_, 6);
v_openDecls_1559_ = lean_ctor_get(v___y_1543_, 7);
v_initHeartbeats_1560_ = lean_ctor_get(v___y_1543_, 8);
v_maxHeartbeats_1561_ = lean_ctor_get(v___y_1543_, 9);
v_quotContext_1562_ = lean_ctor_get(v___y_1543_, 10);
v_currMacroScope_1563_ = lean_ctor_get(v___y_1543_, 11);
v_diag_1564_ = lean_ctor_get_uint8(v___y_1543_, sizeof(void*)*14);
v_cancelTk_x3f_1565_ = lean_ctor_get(v___y_1543_, 12);
v_suppressElabErrors_1566_ = lean_ctor_get_uint8(v___y_1543_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1567_ = lean_ctor_get(v___y_1543_, 13);
v_ref_1568_ = l_Lean_replaceRef(v_stx_1541_, v_ref_1557_);
lean_dec_ref(v_stx_1541_);
lean_inc_ref(v_inheritedTraceOptions_1567_);
lean_inc(v_cancelTk_x3f_1565_);
lean_inc(v_currMacroScope_1563_);
lean_inc(v_quotContext_1562_);
lean_inc(v_maxHeartbeats_1561_);
lean_inc(v_initHeartbeats_1560_);
lean_inc(v_openDecls_1559_);
lean_inc(v_currNamespace_1558_);
lean_inc(v_maxRecDepth_1556_);
lean_inc(v_currRecDepth_1555_);
lean_inc_ref(v_options_1554_);
lean_inc_ref(v_fileMap_1553_);
lean_inc_ref(v_fileName_1552_);
v___x_1569_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1569_, 0, v_fileName_1552_);
lean_ctor_set(v___x_1569_, 1, v_fileMap_1553_);
lean_ctor_set(v___x_1569_, 2, v_options_1554_);
lean_ctor_set(v___x_1569_, 3, v_currRecDepth_1555_);
lean_ctor_set(v___x_1569_, 4, v_maxRecDepth_1556_);
lean_ctor_set(v___x_1569_, 5, v_ref_1568_);
lean_ctor_set(v___x_1569_, 6, v_currNamespace_1558_);
lean_ctor_set(v___x_1569_, 7, v_openDecls_1559_);
lean_ctor_set(v___x_1569_, 8, v_initHeartbeats_1560_);
lean_ctor_set(v___x_1569_, 9, v_maxHeartbeats_1561_);
lean_ctor_set(v___x_1569_, 10, v_quotContext_1562_);
lean_ctor_set(v___x_1569_, 11, v_currMacroScope_1563_);
lean_ctor_set(v___x_1569_, 12, v_cancelTk_x3f_1565_);
lean_ctor_set(v___x_1569_, 13, v_inheritedTraceOptions_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*14, v_diag_1564_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*14 + 1, v_suppressElabErrors_1566_);
lean_inc(v___y_1544_);
v___x_1570_ = lean_apply_4(v_k_1542_, v_val_1546_, v___x_1569_, v___y_1544_, lean_box(0));
return v___x_1570_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_k_1542_);
v___x_1571_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1572_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1541_, v___x_1571_, v___y_1543_, v___y_1544_);
lean_dec(v_stx_1541_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1573_, lean_object* v_k_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1573_, v_k_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_fileName_1584_; lean_object* v_fileMap_1585_; lean_object* v_options_1586_; lean_object* v_currRecDepth_1587_; lean_object* v_maxRecDepth_1588_; lean_object* v_ref_1589_; lean_object* v_currNamespace_1590_; lean_object* v_openDecls_1591_; lean_object* v_initHeartbeats_1592_; lean_object* v_maxHeartbeats_1593_; lean_object* v_quotContext_1594_; lean_object* v_currMacroScope_1595_; uint8_t v_diag_1596_; lean_object* v_cancelTk_x3f_1597_; uint8_t v_suppressElabErrors_1598_; lean_object* v_inheritedTraceOptions_1599_; lean_object* v___x_1600_; lean_object* v_ref_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_fileName_1584_ = lean_ctor_get(v_a_1581_, 0);
v_fileMap_1585_ = lean_ctor_get(v_a_1581_, 1);
v_options_1586_ = lean_ctor_get(v_a_1581_, 2);
v_currRecDepth_1587_ = lean_ctor_get(v_a_1581_, 3);
v_maxRecDepth_1588_ = lean_ctor_get(v_a_1581_, 4);
v_ref_1589_ = lean_ctor_get(v_a_1581_, 5);
v_currNamespace_1590_ = lean_ctor_get(v_a_1581_, 6);
v_openDecls_1591_ = lean_ctor_get(v_a_1581_, 7);
v_initHeartbeats_1592_ = lean_ctor_get(v_a_1581_, 8);
v_maxHeartbeats_1593_ = lean_ctor_get(v_a_1581_, 9);
v_quotContext_1594_ = lean_ctor_get(v_a_1581_, 10);
v_currMacroScope_1595_ = lean_ctor_get(v_a_1581_, 11);
v_diag_1596_ = lean_ctor_get_uint8(v_a_1581_, sizeof(void*)*14);
v_cancelTk_x3f_1597_ = lean_ctor_get(v_a_1581_, 12);
v_suppressElabErrors_1598_ = lean_ctor_get_uint8(v_a_1581_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1599_ = lean_ctor_get(v_a_1581_, 13);
v___x_1600_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1601_ = l_Lean_replaceRef(v_stx_1580_, v_ref_1589_);
lean_inc_ref(v_inheritedTraceOptions_1599_);
lean_inc(v_cancelTk_x3f_1597_);
lean_inc(v_currMacroScope_1595_);
lean_inc(v_quotContext_1594_);
lean_inc(v_maxHeartbeats_1593_);
lean_inc(v_initHeartbeats_1592_);
lean_inc(v_openDecls_1591_);
lean_inc(v_currNamespace_1590_);
lean_inc(v_maxRecDepth_1588_);
lean_inc(v_currRecDepth_1587_);
lean_inc_ref(v_options_1586_);
lean_inc_ref(v_fileMap_1585_);
lean_inc_ref(v_fileName_1584_);
v___x_1602_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1602_, 0, v_fileName_1584_);
lean_ctor_set(v___x_1602_, 1, v_fileMap_1585_);
lean_ctor_set(v___x_1602_, 2, v_options_1586_);
lean_ctor_set(v___x_1602_, 3, v_currRecDepth_1587_);
lean_ctor_set(v___x_1602_, 4, v_maxRecDepth_1588_);
lean_ctor_set(v___x_1602_, 5, v_ref_1601_);
lean_ctor_set(v___x_1602_, 6, v_currNamespace_1590_);
lean_ctor_set(v___x_1602_, 7, v_openDecls_1591_);
lean_ctor_set(v___x_1602_, 8, v_initHeartbeats_1592_);
lean_ctor_set(v___x_1602_, 9, v_maxHeartbeats_1593_);
lean_ctor_set(v___x_1602_, 10, v_quotContext_1594_);
lean_ctor_set(v___x_1602_, 11, v_currMacroScope_1595_);
lean_ctor_set(v___x_1602_, 12, v_cancelTk_x3f_1597_);
lean_ctor_set(v___x_1602_, 13, v_inheritedTraceOptions_1599_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*14, v_diag_1596_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*14 + 1, v_suppressElabErrors_1598_);
v___x_1603_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1580_, v___x_1600_, v___x_1602_, v_a_1582_);
lean_dec_ref(v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_realizeGlobalConst(v_stx_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1608_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_instMonadEIO(lean_box(0));
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_toApplicative_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1649_; 
v___x_1616_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1617_ = l_StateRefT_x27_instMonad___redArg(v___x_1616_);
v_toApplicative_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1617_, 1);
lean_dec(v_unused_1650_);
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1649_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_toApplicative_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1649_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_toFunctor_1622_; lean_object* v_toSeq_1623_; lean_object* v_toSeqLeft_1624_; lean_object* v_toSeqRight_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1647_; 
v_toFunctor_1622_ = lean_ctor_get(v_toApplicative_1618_, 0);
v_toSeq_1623_ = lean_ctor_get(v_toApplicative_1618_, 2);
v_toSeqLeft_1624_ = lean_ctor_get(v_toApplicative_1618_, 3);
v_toSeqRight_1625_ = lean_ctor_get(v_toApplicative_1618_, 4);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_toApplicative_1618_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_toApplicative_1618_, 1);
lean_dec(v_unused_1648_);
v___x_1627_ = v_toApplicative_1618_;
v_isShared_1628_ = v_isSharedCheck_1647_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_toSeqRight_1625_);
lean_inc(v_toSeqLeft_1624_);
lean_inc(v_toSeq_1623_);
lean_inc(v_toFunctor_1622_);
lean_dec(v_toApplicative_1618_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1647_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___x_1638_; 
v___f_1629_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1630_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1622_);
v___f_1631_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1631_, 0, v_toFunctor_1622_);
v___f_1632_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1632_, 0, v_toFunctor_1622_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___f_1631_);
lean_ctor_set(v___x_1633_, 1, v___f_1632_);
v___f_1634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1634_, 0, v_toSeqRight_1625_);
v___f_1635_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1635_, 0, v_toSeqLeft_1624_);
v___f_1636_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1636_, 0, v_toSeq_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v___f_1634_);
lean_ctor_set(v___x_1627_, 3, v___f_1635_);
lean_ctor_set(v___x_1627_, 2, v___f_1636_);
lean_ctor_set(v___x_1627_, 1, v___f_1629_);
lean_ctor_set(v___x_1627_, 0, v___x_1633_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___f_1629_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v___f_1636_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___f_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v___f_1634_);
v___x_1638_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___f_1630_);
lean_ctor_set(v___x_1620_, 0, v___x_1638_);
v___x_1640_ = v___x_1620_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___f_1630_);
v___x_1640_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_195__overap_1643_; lean_object* v___x_1644_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = l_instInhabitedOfMonad___redArg(v___x_1640_, v___x_1641_);
v___x_195__overap_1643_ = lean_panic_fn(v___x_1642_, v_msg_1612_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1644_ = lean_apply_3(v___x_195__overap_1643_, v___y_1613_, v___y_1614_, lean_box(0));
return v___x_1644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
return v_x_1657_;
}
else
{
lean_object* v_head_1659_; lean_object* v_tail_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_head_1659_ = lean_ctor_get(v_x_1658_, 0);
v_tail_1660_ = lean_ctor_get(v_x_1658_, 1);
v___x_1661_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1662_ = lean_string_append(v_x_1657_, v___x_1661_);
v___x_1663_ = lean_expr_dbg_to_string(v_head_1659_);
v___x_1664_ = lean_string_append(v___x_1662_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v_x_1657_ = v___x_1664_;
v_x_1658_ = v_tail_1660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1666_, v_x_1667_);
lean_dec(v_x_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1673_;
}
else
{
lean_object* v_tail_1674_; 
v_tail_1674_ = lean_ctor_get(v_x_1672_, 1);
if (lean_obj_tag(v_tail_1674_) == 0)
{
lean_object* v_head_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_head_1675_ = lean_ctor_get(v_x_1672_, 0);
v___x_1676_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1677_ = lean_expr_dbg_to_string(v_head_1675_);
v___x_1678_ = lean_string_append(v___x_1676_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v_head_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint32_t v___x_1686_; lean_object* v___x_1687_; 
v_head_1681_ = lean_ctor_get(v_x_1672_, 0);
v___x_1682_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1683_ = lean_expr_dbg_to_string(v_head_1681_);
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1684_, v_tail_1674_);
v___x_1686_ = 93;
v___x_1687_ = lean_string_push(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1688_);
lean_dec(v_x_1688_);
return v_res_1689_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1693_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1694_ = lean_unsigned_to_nat(11u);
v___x_1695_ = lean_unsigned_to_nat(429u);
v___x_1696_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1697_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1701_, lean_object* v_cs_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
if (lean_obj_tag(v_cs_1702_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_id_1701_);
v___x_1706_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1707_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1706_, v___y_1703_, v___y_1704_);
return v___x_1707_;
}
else
{
lean_object* v_tail_1708_; 
v_tail_1708_ = lean_ctor_get(v_cs_1702_, 1);
if (lean_obj_tag(v_tail_1708_) == 0)
{
lean_object* v_head_1709_; lean_object* v___x_1710_; 
lean_dec(v_id_1701_);
v_head_1709_ = lean_ctor_get(v_cs_1702_, 0);
lean_inc(v_head_1709_);
lean_dec_ref(v_cs_1702_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_head_1709_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1711_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1712_ = lean_box(0);
v___x_1713_ = 0;
lean_inc(v_id_1701_);
v___x_1714_ = l_Lean_Syntax_formatStx(v_id_1701_, v___x_1712_, v___x_1713_);
v___x_1715_ = l_Std_Format_defWidth;
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = l_Std_Format_pretty(v___x_1714_, v___x_1715_, v___x_1716_, v___x_1716_);
v___x_1718_ = lean_string_append(v___x_1711_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_box(0);
v___x_1722_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1702_, v___x_1721_);
v___x_1723_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1722_);
lean_dec(v___x_1722_);
v___x_1724_ = lean_string_append(v___x_1720_, v___x_1723_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
v___x_1726_ = l_Lean_MessageData_ofFormat(v___x_1725_);
v___x_1727_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1701_, v___x_1726_, v___y_1703_, v___y_1704_);
lean_dec(v_id_1701_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1728_, lean_object* v_cs_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1728_, v_cs_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; 
lean_inc(v_id_1734_);
v___x_1738_ = l_Lean_realizeGlobalConst(v_id_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1734_, v_a_1739_, v_a_1735_, v_a_1736_);
return v___x_1740_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_id_1734_);
v_a_1741_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1738_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1738_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_realizeGlobalConstNoOverload(v_id_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1753_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(3863082579u);
v___x_1786_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1787_ = l_Lean_Name_num___override(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1790_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1791_ = l_Lean_Name_str___override(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1794_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1795_ = l_Lean_Name_str___override(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_unsigned_to_nat(2u);
v___x_1797_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1798_ = l_Lean_Name_num___override(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1801_ = 0;
v___x_1802_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1803_ = l_Lean_registerTraceClass(v___x_1800_, v___x_1801_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1805_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef);
lean_dec_ref(res);
res = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ReservedNameAction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ReservedNameAction(builtin);
}
#ifdef __cplusplus
}
#endif

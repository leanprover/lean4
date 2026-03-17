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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* v___x_4914__overap_167_; lean_object* v___x_168_; 
v___x_4914__overap_167_ = lean_array_uget_borrowed(v_as_160_, v_i_161_);
lean_inc(v___x_4914__overap_167_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v_name_159_);
v___x_168_ = lean_apply_4(v___x_4914__overap_167_, v_name_159_, v___y_163_, v___y_164_, lean_box(0));
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
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
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
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v_name_159_);
return v___x_168_;
}
}
else
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
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
lean_object* v_fileName_296_; lean_object* v_fileMap_297_; lean_object* v_options_298_; lean_object* v_currRecDepth_299_; lean_object* v_maxRecDepth_300_; lean_object* v_ref_301_; lean_object* v_currNamespace_302_; lean_object* v_openDecls_303_; lean_object* v_initHeartbeats_304_; lean_object* v_maxHeartbeats_305_; lean_object* v_quotContext_306_; lean_object* v_currMacroScope_307_; uint8_t v_diag_308_; lean_object* v_cancelTk_x3f_309_; uint8_t v_suppressElabErrors_310_; lean_object* v_inheritedTraceOptions_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_366_; 
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
v_isSharedCheck_366_ = !lean_is_exclusive(v___y_293_);
if (v_isSharedCheck_366_ == 0)
{
v___x_313_ = v___y_293_;
v_isShared_314_ = v_isSharedCheck_366_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_inheritedTraceOptions_311_);
lean_inc(v_cancelTk_x3f_309_);
lean_inc(v_currMacroScope_307_);
lean_inc(v_quotContext_306_);
lean_inc(v_maxHeartbeats_305_);
lean_inc(v_initHeartbeats_304_);
lean_inc(v_openDecls_303_);
lean_inc(v_currNamespace_302_);
lean_inc(v_ref_301_);
lean_inc(v_maxRecDepth_300_);
lean_inc(v_currRecDepth_299_);
lean_inc(v_options_298_);
lean_inc(v_fileMap_297_);
lean_inc(v_fileName_296_);
lean_dec(v___y_293_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_366_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v_traceState_316_; lean_object* v_traces_317_; lean_object* v_ref_318_; lean_object* v___x_320_; 
v___x_315_ = lean_st_ref_get(v___y_294_);
v_traceState_316_ = lean_ctor_get(v___x_315_, 4);
lean_inc_ref(v_traceState_316_);
lean_dec(v___x_315_);
v_traces_317_ = lean_ctor_get(v_traceState_316_, 0);
lean_inc_ref(v_traces_317_);
lean_dec_ref(v_traceState_316_);
v_ref_318_ = l_Lean_replaceRef(v_ref_291_, v_ref_301_);
lean_dec(v_ref_301_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 5, v_ref_318_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fileName_296_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_fileMap_297_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_options_298_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_currRecDepth_299_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_maxRecDepth_300_);
lean_ctor_set(v_reuseFailAlloc_365_, 5, v_ref_318_);
lean_ctor_set(v_reuseFailAlloc_365_, 6, v_currNamespace_302_);
lean_ctor_set(v_reuseFailAlloc_365_, 7, v_openDecls_303_);
lean_ctor_set(v_reuseFailAlloc_365_, 8, v_initHeartbeats_304_);
lean_ctor_set(v_reuseFailAlloc_365_, 9, v_maxHeartbeats_305_);
lean_ctor_set(v_reuseFailAlloc_365_, 10, v_quotContext_306_);
lean_ctor_set(v_reuseFailAlloc_365_, 11, v_currMacroScope_307_);
lean_ctor_set(v_reuseFailAlloc_365_, 12, v_cancelTk_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_365_, 13, v_inheritedTraceOptions_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_365_, sizeof(void*)*14, v_diag_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_365_, sizeof(void*)*14 + 1, v_suppressElabErrors_310_);
v___x_320_ = v_reuseFailAlloc_365_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; size_t v_sz_322_; size_t v___x_323_; lean_object* v___x_324_; lean_object* v_msg_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_364_; 
v___x_321_ = l_Lean_PersistentArray_toArray___redArg(v_traces_317_);
lean_dec_ref(v_traces_317_);
v_sz_322_ = lean_array_size(v___x_321_);
v___x_323_ = ((size_t)0ULL);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__6(v_sz_322_, v___x_323_, v___x_321_);
v_msg_325_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_325_, 0, v_data_290_);
lean_ctor_set(v_msg_325_, 1, v_msg_292_);
lean_ctor_set(v_msg_325_, 2, v___x_324_);
v___x_326_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v_msg_325_, v___x_320_, v___y_294_);
lean_dec_ref(v___x_320_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_364_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_364_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_364_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v_traceState_332_; lean_object* v_env_333_; lean_object* v_nextMacroScope_334_; lean_object* v_ngen_335_; lean_object* v_auxDeclNGen_336_; lean_object* v_cache_337_; lean_object* v_messages_338_; lean_object* v_infoState_339_; lean_object* v_snapshotTasks_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_363_; 
v___x_331_ = lean_st_ref_take(v___y_294_);
v_traceState_332_ = lean_ctor_get(v___x_331_, 4);
v_env_333_ = lean_ctor_get(v___x_331_, 0);
v_nextMacroScope_334_ = lean_ctor_get(v___x_331_, 1);
v_ngen_335_ = lean_ctor_get(v___x_331_, 2);
v_auxDeclNGen_336_ = lean_ctor_get(v___x_331_, 3);
v_cache_337_ = lean_ctor_get(v___x_331_, 5);
v_messages_338_ = lean_ctor_get(v___x_331_, 6);
v_infoState_339_ = lean_ctor_get(v___x_331_, 7);
v_snapshotTasks_340_ = lean_ctor_get(v___x_331_, 8);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_363_ == 0)
{
v___x_342_ = v___x_331_;
v_isShared_343_ = v_isSharedCheck_363_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snapshotTasks_340_);
lean_inc(v_infoState_339_);
lean_inc(v_messages_338_);
lean_inc(v_cache_337_);
lean_inc(v_traceState_332_);
lean_inc(v_auxDeclNGen_336_);
lean_inc(v_ngen_335_);
lean_inc(v_nextMacroScope_334_);
lean_inc(v_env_333_);
lean_dec(v___x_331_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_363_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint64_t v_tid_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_361_; 
v_tid_344_ = lean_ctor_get_uint64(v_traceState_332_, sizeof(void*)*1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_traceState_332_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v_traceState_332_, 0);
lean_dec(v_unused_362_);
v___x_346_ = v_traceState_332_;
v_isShared_347_ = v_isSharedCheck_361_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_traceState_332_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_361_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_ref_291_);
lean_ctor_set(v___x_348_, 1, v_a_327_);
v___x_349_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_289_, v___x_348_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_349_);
lean_ctor_set_uint64(v_reuseFailAlloc_360_, sizeof(void*)*1, v_tid_344_);
v___x_351_ = v_reuseFailAlloc_360_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_351_);
v___x_353_ = v___x_342_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_env_333_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_nextMacroScope_334_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_ngen_335_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_auxDeclNGen_336_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_359_, 5, v_cache_337_);
lean_ctor_set(v_reuseFailAlloc_359_, 6, v_messages_338_);
lean_ctor_set(v_reuseFailAlloc_359_, 7, v_infoState_339_);
lean_ctor_set(v_reuseFailAlloc_359_, 8, v_snapshotTasks_340_);
v___x_353_ = v_reuseFailAlloc_359_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_354_ = lean_st_ref_set(v___y_294_, v___x_353_);
v___x_355_ = lean_box(0);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_355_);
v___x_357_ = v___x_329_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5___boxed(lean_object* v_oldTraces_367_, lean_object* v_data_368_, lean_object* v_ref_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(v_oldTraces_367_, v_data_368_, v_ref_369_, v_msg_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
return v_res_374_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__0));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2(void){
_start:
{
lean_object* v___x_378_; double v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_float_of_nat(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__3));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5(void){
_start:
{
lean_object* v___x_383_; double v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(1000u);
v___x_384_ = lean_float_of_nat(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(lean_object* v_cls_385_, uint8_t v_collapsed_386_, lean_object* v_tag_387_, lean_object* v_opts_388_, uint8_t v_clsEnabled_389_, lean_object* v_oldTraces_390_, lean_object* v_msg_391_, lean_object* v_resStartStop_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_495_; 
v_fst_396_ = lean_ctor_get(v_resStartStop_392_, 0);
v_snd_397_ = lean_ctor_get(v_resStartStop_392_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_resStartStop_392_);
if (v_isSharedCheck_495_ == 0)
{
v___x_399_ = v_resStartStop_392_;
v_isShared_400_ = v_isSharedCheck_495_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_resStartStop_392_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_495_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v_data_404_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_494_; 
v_fst_415_ = lean_ctor_get(v_snd_397_, 0);
v_snd_416_ = lean_ctor_get(v_snd_397_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_snd_397_);
if (v_isSharedCheck_494_ == 0)
{
v___x_418_ = v_snd_397_;
v_isShared_419_ = v_isSharedCheck_494_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snd_416_);
lean_inc(v_fst_415_);
lean_dec(v_snd_397_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_494_;
goto v_resetjp_417_;
}
v___jp_401_:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5(v_oldTraces_390_, v_data_404_, v___y_402_, v___y_403_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_405_);
v___x_406_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_fst_396_);
return v___x_406_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_fst_396_);
v_a_407_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
v_resetjp_417_:
{
lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___y_423_; lean_object* v_a_424_; uint8_t v___y_448_; double v___y_479_; 
v___x_420_ = l_Lean_trace_profiler;
v___x_421_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_opts_388_, v___x_420_);
if (v___x_421_ == 0)
{
v___y_448_ = v___x_421_;
goto v___jp_447_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = l_Lean_trace_profiler_useHeartbeats;
v___x_485_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_opts_388_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; double v___x_488_; double v___x_489_; double v___x_490_; 
v___x_486_ = l_Lean_trace_profiler_threshold;
v___x_487_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(v_opts_388_, v___x_486_);
v___x_488_ = lean_float_of_nat(v___x_487_);
v___x_489_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__5);
v___x_490_ = lean_float_div(v___x_488_, v___x_489_);
v___y_479_ = v___x_490_;
goto v___jp_478_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; double v___x_493_; 
v___x_491_ = l_Lean_trace_profiler_threshold;
v___x_492_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__7(v_opts_388_, v___x_491_);
v___x_493_ = lean_float_of_nat(v___x_492_);
v___y_479_ = v___x_493_;
goto v___jp_478_;
}
}
v___jp_422_:
{
uint8_t v_result_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_result_425_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__4(v_fst_396_);
v___x_426_ = l_Lean_TraceResult_toEmoji(v_result_425_);
v___x_427_ = l_Lean_stringToMessageData(v___x_426_);
v___x_428_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__1);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 7);
lean_ctor_set(v___x_418_, 1, v___x_428_);
lean_ctor_set(v___x_418_, 0, v___x_427_);
v___x_430_ = v___x_418_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_441_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v_m_432_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 7);
lean_ctor_set(v___x_399_, 1, v_a_424_);
lean_ctor_set(v___x_399_, 0, v___x_430_);
v_m_432_ = v___x_399_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_a_424_);
v_m_432_ = v_reuseFailAlloc_440_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; double v___x_435_; lean_object* v_data_436_; 
v___x_433_ = lean_box(v_result_425_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
v___x_435_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__2);
lean_inc_ref(v_tag_387_);
lean_inc_ref(v___x_434_);
lean_inc(v_cls_385_);
v_data_436_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_436_, 0, v_cls_385_);
lean_ctor_set(v_data_436_, 1, v___x_434_);
lean_ctor_set(v_data_436_, 2, v_tag_387_);
lean_ctor_set_float(v_data_436_, sizeof(void*)*3, v___x_435_);
lean_ctor_set_float(v_data_436_, sizeof(void*)*3 + 8, v___x_435_);
lean_ctor_set_uint8(v_data_436_, sizeof(void*)*3 + 16, v_collapsed_386_);
if (v___x_421_ == 0)
{
lean_dec_ref(v___x_434_);
lean_dec(v_snd_416_);
lean_dec(v_fst_415_);
lean_dec_ref(v_tag_387_);
lean_dec(v_cls_385_);
v___y_402_ = v___y_423_;
v___y_403_ = v_m_432_;
v_data_404_ = v_data_436_;
goto v___jp_401_;
}
else
{
lean_object* v_data_437_; double v___x_438_; double v___x_439_; 
lean_dec_ref(v_data_436_);
v_data_437_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_437_, 0, v_cls_385_);
lean_ctor_set(v_data_437_, 1, v___x_434_);
lean_ctor_set(v_data_437_, 2, v_tag_387_);
v___x_438_ = lean_unbox_float(v_fst_415_);
lean_dec(v_fst_415_);
lean_ctor_set_float(v_data_437_, sizeof(void*)*3, v___x_438_);
v___x_439_ = lean_unbox_float(v_snd_416_);
lean_dec(v_snd_416_);
lean_ctor_set_float(v_data_437_, sizeof(void*)*3 + 8, v___x_439_);
lean_ctor_set_uint8(v_data_437_, sizeof(void*)*3 + 16, v_collapsed_386_);
v___y_402_ = v___y_423_;
v___y_403_ = v_m_432_;
v_data_404_ = v_data_437_;
goto v___jp_401_;
}
}
}
}
v___jp_442_:
{
lean_object* v_ref_443_; lean_object* v___x_444_; 
v_ref_443_ = lean_ctor_get(v___y_393_, 5);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v_fst_396_);
v___x_444_ = lean_apply_4(v_msg_391_, v_fst_396_, v___y_393_, v___y_394_, lean_box(0));
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_444_);
lean_inc(v_ref_443_);
v___y_423_ = v_ref_443_;
v_a_424_ = v_a_445_;
goto v___jp_422_;
}
else
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___closed__4);
lean_inc(v_ref_443_);
v___y_423_ = v_ref_443_;
v_a_424_ = v___x_446_;
goto v___jp_422_;
}
}
v___jp_447_:
{
if (v_clsEnabled_389_ == 0)
{
if (v___y_448_ == 0)
{
lean_object* v___x_449_; lean_object* v_traceState_450_; lean_object* v_env_451_; lean_object* v_nextMacroScope_452_; lean_object* v_ngen_453_; lean_object* v_auxDeclNGen_454_; lean_object* v_cache_455_; lean_object* v_messages_456_; lean_object* v_infoState_457_; lean_object* v_snapshotTasks_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_418_);
lean_dec(v_snd_416_);
lean_dec(v_fst_415_);
lean_del_object(v___x_399_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_msg_391_);
lean_dec_ref(v_tag_387_);
lean_dec(v_cls_385_);
v___x_449_ = lean_st_ref_take(v___y_394_);
v_traceState_450_ = lean_ctor_get(v___x_449_, 4);
v_env_451_ = lean_ctor_get(v___x_449_, 0);
v_nextMacroScope_452_ = lean_ctor_get(v___x_449_, 1);
v_ngen_453_ = lean_ctor_get(v___x_449_, 2);
v_auxDeclNGen_454_ = lean_ctor_get(v___x_449_, 3);
v_cache_455_ = lean_ctor_get(v___x_449_, 5);
v_messages_456_ = lean_ctor_get(v___x_449_, 6);
v_infoState_457_ = lean_ctor_get(v___x_449_, 7);
v_snapshotTasks_458_ = lean_ctor_get(v___x_449_, 8);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_477_ == 0)
{
v___x_460_ = v___x_449_;
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_snapshotTasks_458_);
lean_inc(v_infoState_457_);
lean_inc(v_messages_456_);
lean_inc(v_cache_455_);
lean_inc(v_traceState_450_);
lean_inc(v_auxDeclNGen_454_);
lean_inc(v_ngen_453_);
lean_inc(v_nextMacroScope_452_);
lean_inc(v_env_451_);
lean_dec(v___x_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint64_t v_tid_462_; lean_object* v_traces_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_476_; 
v_tid_462_ = lean_ctor_get_uint64(v_traceState_450_, sizeof(void*)*1);
v_traces_463_ = lean_ctor_get(v_traceState_450_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_traceState_450_);
if (v_isSharedCheck_476_ == 0)
{
v___x_465_ = v_traceState_450_;
v_isShared_466_ = v_isSharedCheck_476_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_traces_463_);
lean_dec(v_traceState_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_476_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_390_, v_traces_463_);
lean_dec_ref(v_traces_463_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_467_);
lean_ctor_set_uint64(v_reuseFailAlloc_475_, sizeof(void*)*1, v_tid_462_);
v___x_469_ = v_reuseFailAlloc_475_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 4, v___x_469_);
v___x_471_ = v___x_460_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_env_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_nextMacroScope_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_ngen_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_auxDeclNGen_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_cache_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_messages_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_infoState_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_snapshotTasks_458_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_st_ref_set(v___y_394_, v___x_471_);
lean_dec(v___y_394_);
v___x_473_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_fst_396_);
return v___x_473_;
}
}
}
}
}
else
{
goto v___jp_442_;
}
}
else
{
goto v___jp_442_;
}
}
v___jp_478_:
{
double v___x_480_; double v___x_481_; double v___x_482_; uint8_t v___x_483_; 
v___x_480_ = lean_unbox_float(v_snd_416_);
v___x_481_ = lean_unbox_float(v_fst_415_);
v___x_482_ = lean_float_sub(v___x_480_, v___x_481_);
v___x_483_ = lean_float_decLt(v___y_479_, v___x_482_);
v___y_448_ = v___x_483_;
goto v___jp_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4___boxed(lean_object* v_cls_496_, lean_object* v_collapsed_497_, lean_object* v_tag_498_, lean_object* v_opts_499_, lean_object* v_clsEnabled_500_, lean_object* v_oldTraces_501_, lean_object* v_msg_502_, lean_object* v_resStartStop_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v_collapsed_boxed_507_; uint8_t v_clsEnabled_boxed_508_; lean_object* v_res_509_; 
v_collapsed_boxed_507_ = lean_unbox(v_collapsed_497_);
v_clsEnabled_boxed_508_ = lean_unbox(v_clsEnabled_500_);
v_res_509_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v_cls_496_, v_collapsed_boxed_507_, v_tag_498_, v_opts_499_, v_clsEnabled_boxed_508_, v_oldTraces_501_, v_msg_502_, v_resStartStop_503_, v___y_504_, v___y_505_);
lean_dec_ref(v_opts_499_);
return v_res_509_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__3(void){
_start:
{
lean_object* v___x_514_; double v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1000000000u);
v___x_515_ = lean_float_of_nat(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_options_520_; uint8_t v_hasTrace_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___y_525_; 
v_options_520_ = lean_ctor_get(v_a_517_, 2);
v_hasTrace_521_ = lean_ctor_get_uint8(v_options_520_, sizeof(void*)*1);
v___x_522_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_523_ = lean_box(0);
if (v_hasTrace_521_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_st_ref_get(v___x_522_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v___x_542_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v___x_542_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_name_516_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_523_);
return v___x_546_;
}
else
{
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v___x_542_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_name_516_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_523_);
return v___x_547_;
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_544_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_516_, v___x_542_, v___x_548_, v___x_549_, v_a_517_, v_a_518_);
lean_dec(v___x_542_);
v___y_525_ = v___x_550_;
goto v___jp_524_;
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_657_; 
v___x_551_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_552_ = l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg(v___x_551_, v_a_517_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_657_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_657_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_657_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v_a_562_; lean_object* v___y_576_; lean_object* v___y_577_; uint8_t v_a_578_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v_a_584_; lean_object* v___y_595_; lean_object* v___y_596_; uint8_t v_a_597_; uint8_t v___x_641_; 
lean_inc(v_name_516_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_557_, 0, v_name_516_);
v___x_558_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_641_ = lean_unbox(v_a_553_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = l_Lean_trace_profiler;
v___x_643_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_520_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
lean_dec_ref(v___f_557_);
lean_dec(v_a_553_);
v___x_644_ = lean_st_ref_get(v___x_522_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v___x_644_);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_649_; 
lean_dec(v___x_644_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_name_516_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_523_);
v___x_649_ = v___x_555_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_523_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
if (v___x_647_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_644_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_name_516_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_523_);
v___x_652_ = v___x_555_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_523_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_555_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_646_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_516_, v___x_644_, v___x_654_, v___x_655_, v_a_517_, v_a_518_);
lean_dec(v___x_644_);
v___y_525_ = v___x_656_;
goto v___jp_524_;
}
}
}
else
{
lean_inc_ref(v_options_520_);
lean_del_object(v___x_555_);
goto v___jp_600_;
}
}
else
{
lean_inc_ref(v_options_520_);
lean_del_object(v___x_555_);
goto v___jp_600_;
}
v___jp_559_:
{
lean_object* v___x_563_; double v___x_564_; double v___x_565_; double v___x_566_; double v___x_567_; double v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; 
v___x_563_ = lean_io_mono_nanos_now();
v___x_564_ = lean_float_of_nat(v___y_560_);
v___x_565_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__3, &l_Lean_executeReservedNameAction___closed__3_once, _init_l_Lean_executeReservedNameAction___closed__3);
v___x_566_ = lean_float_div(v___x_564_, v___x_565_);
v___x_567_ = lean_float_of_nat(v___x_563_);
v___x_568_ = lean_float_div(v___x_567_, v___x_565_);
v___x_569_ = lean_box_float(v___x_566_);
v___x_570_ = lean_box_float(v___x_568_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_562_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_unbox(v_a_553_);
lean_dec(v_a_553_);
v___x_574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v___x_551_, v_hasTrace_521_, v___x_558_, v_options_520_, v___x_573_, v___y_561_, v___f_557_, v___x_572_, v_a_517_, v_a_518_);
lean_dec_ref(v_options_520_);
v___y_525_ = v___x_574_;
goto v___jp_524_;
}
v___jp_575_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(v_a_578_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___y_560_ = v___y_576_;
v___y_561_ = v___y_577_;
v_a_562_ = v___x_580_;
goto v___jp_559_;
}
v___jp_581_:
{
lean_object* v___x_585_; double v___x_586_; double v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_585_ = lean_io_get_num_heartbeats();
v___x_586_ = lean_float_of_nat(v___y_583_);
v___x_587_ = lean_float_of_nat(v___x_585_);
v___x_588_ = lean_box_float(v___x_586_);
v___x_589_ = lean_box_float(v___x_587_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_584_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_unbox(v_a_553_);
lean_dec(v_a_553_);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4(v___x_551_, v_hasTrace_521_, v___x_558_, v_options_520_, v___x_592_, v___y_582_, v___f_557_, v___x_591_, v_a_517_, v_a_518_);
lean_dec_ref(v_options_520_);
v___y_525_ = v___x_593_;
goto v___jp_524_;
}
v___jp_594_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(v_a_597_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v_a_584_ = v___x_599_;
goto v___jp_581_;
}
v___jp_600_:
{
lean_object* v___x_601_; lean_object* v_a_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__2___redArg(v_a_518_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___x_601_);
v___x_603_ = l_Lean_trace_profiler_useHeartbeats;
v___x_604_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_520_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_605_ = lean_io_mono_nanos_now();
v___x_606_ = lean_st_ref_get(v___x_522_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_array_get_size(v___x_606_);
v___x_609_ = lean_nat_dec_lt(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v___x_606_);
lean_dec(v_name_516_);
v___y_576_ = v___x_605_;
v___y_577_ = v_a_602_;
v_a_578_ = v___x_604_;
goto v___jp_575_;
}
else
{
if (v___x_609_ == 0)
{
lean_dec(v___x_606_);
lean_dec(v_name_516_);
v___y_576_ = v___x_605_;
v___y_577_ = v_a_602_;
v_a_578_ = v___x_604_;
goto v___jp_575_;
}
else
{
size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_608_);
lean_inc(v_a_518_);
lean_inc_ref(v_a_517_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_516_, v___x_606_, v___x_610_, v___x_611_, v_a_517_, v_a_518_);
lean_dec(v___x_606_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; uint8_t v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_612_);
v___x_614_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
v___y_576_ = v___x_605_;
v___y_577_ = v_a_602_;
v_a_578_ = v___x_614_;
goto v___jp_575_;
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_612_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 0);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v___y_560_ = v___x_605_;
v___y_561_ = v_a_602_;
v_a_562_ = v___x_620_;
goto v___jp_559_;
}
}
}
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_623_ = lean_io_get_num_heartbeats();
v___x_624_ = lean_st_ref_get(v___x_522_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_array_get_size(v___x_624_);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v___x_624_);
lean_dec(v_name_516_);
v___y_595_ = v_a_602_;
v___y_596_ = v___x_623_;
v_a_597_ = v___x_627_;
goto v___jp_594_;
}
else
{
if (v___x_627_ == 0)
{
lean_dec(v___x_624_);
lean_dec(v_name_516_);
v___y_595_ = v_a_602_;
v___y_596_ = v___x_623_;
v_a_597_ = v___x_627_;
goto v___jp_594_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_626_);
lean_inc(v_a_518_);
lean_inc_ref(v_a_517_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_516_, v___x_624_, v___x_628_, v___x_629_, v_a_517_, v_a_518_);
lean_dec(v___x_624_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; uint8_t v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = lean_unbox(v_a_631_);
lean_dec(v_a_631_);
v___y_595_ = v_a_602_;
v___y_596_ = v___x_623_;
v_a_597_ = v___x_632_;
goto v___jp_594_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_630_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 0);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v___y_582_ = v_a_602_;
v___y_583_ = v___x_623_;
v_a_584_ = v___x_638_;
goto v___jp_581_;
}
}
}
}
}
}
}
}
}
v___jp_524_:
{
if (lean_obj_tag(v___y_525_) == 0)
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_isSharedCheck_532_ = !lean_is_exclusive(v___y_525_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___y_525_, 0);
lean_dec(v_unused_533_);
v___x_527_ = v___y_525_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_dec(v___y_525_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_523_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_523_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___y_525_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___y_525_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___y_525_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___y_525_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_executeReservedNameAction(v_name_658_, v_a_659_, v_a_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6(lean_object* v_00_u03b1_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___redArg(v_x_664_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6___boxed(lean_object* v_00_u03b1_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__6(v_00_u03b1_669_, v_x_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_682_, uint8_t v_suppressElabErrors_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 1)
{
lean_object* v_pre_685_; 
v_pre_685_ = lean_ctor_get(v_x_684_, 0);
switch(lean_obj_tag(v_pre_685_))
{
case 1:
{
lean_object* v_pre_686_; 
v_pre_686_ = lean_ctor_get(v_pre_685_, 0);
switch(lean_obj_tag(v_pre_686_))
{
case 0:
{
lean_object* v_str_687_; lean_object* v_str_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_str_687_ = lean_ctor_get(v_x_684_, 1);
v_str_688_ = lean_ctor_get(v_pre_685_, 1);
v___x_689_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_690_ = lean_string_dec_eq(v_str_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_692_ = lean_string_dec_eq(v_str_688_, v___x_691_);
if (v___x_692_ == 0)
{
return v___y_682_;
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_694_ = lean_string_dec_eq(v_str_687_, v___x_693_);
if (v___x_694_ == 0)
{
return v___y_682_;
}
else
{
return v_suppressElabErrors_683_;
}
}
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_696_ = lean_string_dec_eq(v_str_687_, v___x_695_);
if (v___x_696_ == 0)
{
return v___y_682_;
}
else
{
return v_suppressElabErrors_683_;
}
}
}
case 1:
{
lean_object* v_pre_697_; 
v_pre_697_ = lean_ctor_get(v_pre_686_, 0);
if (lean_obj_tag(v_pre_697_) == 0)
{
lean_object* v_str_698_; lean_object* v_str_699_; lean_object* v_str_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_str_698_ = lean_ctor_get(v_x_684_, 1);
v_str_699_ = lean_ctor_get(v_pre_685_, 1);
v_str_700_ = lean_ctor_get(v_pre_686_, 1);
v___x_701_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_702_ = lean_string_dec_eq(v_str_700_, v___x_701_);
if (v___x_702_ == 0)
{
return v___y_682_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_704_ = lean_string_dec_eq(v_str_699_, v___x_703_);
if (v___x_704_ == 0)
{
return v___y_682_;
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_706_ = lean_string_dec_eq(v_str_698_, v___x_705_);
if (v___x_706_ == 0)
{
return v___y_682_;
}
else
{
return v_suppressElabErrors_683_;
}
}
}
}
else
{
return v___y_682_;
}
}
default: 
{
return v___y_682_;
}
}
}
case 0:
{
lean_object* v_str_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_str_707_ = lean_ctor_get(v_x_684_, 1);
v___x_708_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0));
v___x_709_ = lean_string_dec_eq(v_str_707_, v___x_708_);
if (v___x_709_ == 0)
{
return v___y_682_;
}
else
{
return v_suppressElabErrors_683_;
}
}
default: 
{
return v___y_682_;
}
}
}
else
{
return v___y_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_710_, lean_object* v_suppressElabErrors_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___y_4910__boxed_713_; uint8_t v_suppressElabErrors_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v___y_4910__boxed_713_ = lean_unbox(v___y_710_);
v_suppressElabErrors_boxed_714_ = lean_unbox(v_suppressElabErrors_711_);
v_res_715_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4910__boxed_713_, v_suppressElabErrors_boxed_714_, v_x_712_);
lean_dec(v_x_712_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_717_, lean_object* v_msgData_718_, uint8_t v_severity_719_, uint8_t v_isSilent_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; uint8_t v___y_767_; lean_object* v___y_768_; lean_object* v___y_786_; uint8_t v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_797_; uint8_t v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; uint8_t v___x_808_; uint8_t v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; uint8_t v___y_816_; uint8_t v___y_818_; uint8_t v___x_833_; 
v___x_808_ = 2;
v___x_833_ = l_Lean_instBEqMessageSeverity_beq(v_severity_719_, v___x_808_);
if (v___x_833_ == 0)
{
v___y_818_ = v___x_833_;
goto v___jp_817_;
}
else
{
uint8_t v___x_834_; 
lean_inc_ref(v_msgData_718_);
v___x_834_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_718_);
v___y_818_ = v___x_834_;
goto v___jp_817_;
}
v___jp_724_:
{
lean_object* v___x_734_; lean_object* v_currNamespace_735_; lean_object* v_openDecls_736_; lean_object* v_env_737_; lean_object* v_nextMacroScope_738_; lean_object* v_ngen_739_; lean_object* v_auxDeclNGen_740_; lean_object* v_traceState_741_; lean_object* v_cache_742_; lean_object* v_messages_743_; lean_object* v_infoState_744_; lean_object* v_snapshotTasks_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_759_; 
v___x_734_ = lean_st_ref_take(v___y_733_);
v_currNamespace_735_ = lean_ctor_get(v___y_732_, 6);
lean_inc(v_currNamespace_735_);
v_openDecls_736_ = lean_ctor_get(v___y_732_, 7);
lean_inc(v_openDecls_736_);
lean_dec_ref(v___y_732_);
v_env_737_ = lean_ctor_get(v___x_734_, 0);
v_nextMacroScope_738_ = lean_ctor_get(v___x_734_, 1);
v_ngen_739_ = lean_ctor_get(v___x_734_, 2);
v_auxDeclNGen_740_ = lean_ctor_get(v___x_734_, 3);
v_traceState_741_ = lean_ctor_get(v___x_734_, 4);
v_cache_742_ = lean_ctor_get(v___x_734_, 5);
v_messages_743_ = lean_ctor_get(v___x_734_, 6);
v_infoState_744_ = lean_ctor_get(v___x_734_, 7);
v_snapshotTasks_745_ = lean_ctor_get(v___x_734_, 8);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_759_ == 0)
{
v___x_747_ = v___x_734_;
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snapshotTasks_745_);
lean_inc(v_infoState_744_);
lean_inc(v_messages_743_);
lean_inc(v_cache_742_);
lean_inc(v_traceState_741_);
lean_inc(v_auxDeclNGen_740_);
lean_inc(v_ngen_739_);
lean_inc(v_nextMacroScope_738_);
lean_inc(v_env_737_);
lean_dec(v___x_734_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_currNamespace_735_);
lean_ctor_set(v___x_749_, 1, v_openDecls_736_);
v___x_750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___y_727_);
v___x_751_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_751_, 0, v___y_728_);
lean_ctor_set(v___x_751_, 1, v___y_725_);
lean_ctor_set(v___x_751_, 2, v___y_731_);
lean_ctor_set(v___x_751_, 3, v___y_730_);
lean_ctor_set(v___x_751_, 4, v___x_750_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5, v___y_726_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5 + 1, v___y_729_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5 + 2, v_isSilent_720_);
v___x_752_ = l_Lean_MessageLog_add(v___x_751_, v_messages_743_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 6, v___x_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_env_737_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_nextMacroScope_738_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_ngen_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_auxDeclNGen_740_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_traceState_741_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_cache_742_);
lean_ctor_set(v_reuseFailAlloc_758_, 6, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 7, v_infoState_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 8, v_snapshotTasks_745_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_st_ref_set(v___y_733_, v___x_754_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
v___jp_760_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_784_; 
v___x_769_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_718_);
v___x_770_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v___x_769_, v___y_721_, v___y_722_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_784_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_784_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_784_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_ref(v___y_765_);
v___x_775_ = l_Lean_FileMap_toPosition(v___y_765_, v___y_764_);
lean_dec(v___y_764_);
v___x_776_ = l_Lean_FileMap_toPosition(v___y_765_, v___y_768_);
lean_dec(v___y_768_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_762_ == 0)
{
lean_del_object(v___x_773_);
lean_dec_ref(v___y_761_);
v___y_725_ = v___x_775_;
v___y_726_ = v___y_763_;
v___y_727_ = v_a_771_;
v___y_728_ = v___y_766_;
v___y_729_ = v___y_767_;
v___y_730_ = v___x_778_;
v___y_731_ = v___x_777_;
v___y_732_ = v___y_721_;
v___y_733_ = v___y_722_;
goto v___jp_724_;
}
else
{
uint8_t v___x_779_; 
lean_inc(v_a_771_);
v___x_779_ = l_Lean_MessageData_hasTag(v___y_761_, v_a_771_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec_ref(v___x_777_);
lean_dec_ref(v___x_775_);
lean_dec(v_a_771_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v___y_721_);
v___x_780_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_780_);
v___x_782_ = v___x_773_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_del_object(v___x_773_);
v___y_725_ = v___x_775_;
v___y_726_ = v___y_763_;
v___y_727_ = v_a_771_;
v___y_728_ = v___y_766_;
v___y_729_ = v___y_767_;
v___y_730_ = v___x_778_;
v___y_731_ = v___x_777_;
v___y_732_ = v___y_721_;
v___y_733_ = v___y_722_;
goto v___jp_724_;
}
}
}
}
v___jp_785_:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Syntax_getTailPos_x3f(v___y_792_, v___y_788_);
lean_dec(v___y_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_inc(v___y_793_);
v___y_761_ = v___y_786_;
v___y_762_ = v___y_787_;
v___y_763_ = v___y_788_;
v___y_764_ = v___y_793_;
v___y_765_ = v___y_789_;
v___y_766_ = v___y_790_;
v___y_767_ = v___y_791_;
v___y_768_ = v___y_793_;
goto v___jp_760_;
}
else
{
lean_object* v_val_795_; 
v_val_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref(v___x_794_);
v___y_761_ = v___y_786_;
v___y_762_ = v___y_787_;
v___y_763_ = v___y_788_;
v___y_764_ = v___y_793_;
v___y_765_ = v___y_789_;
v___y_766_ = v___y_790_;
v___y_767_ = v___y_791_;
v___y_768_ = v_val_795_;
goto v___jp_760_;
}
}
v___jp_796_:
{
lean_object* v_ref_804_; lean_object* v___x_805_; 
v_ref_804_ = l_Lean_replaceRef(v_ref_717_, v___y_800_);
lean_dec(v___y_800_);
v___x_805_ = l_Lean_Syntax_getPos_x3f(v_ref_804_, v___y_799_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___y_786_ = v___y_797_;
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___y_801_;
v___y_790_ = v___y_802_;
v___y_791_ = v___y_803_;
v___y_792_ = v_ref_804_;
v___y_793_ = v___x_806_;
goto v___jp_785_;
}
else
{
lean_object* v_val_807_; 
v_val_807_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v___x_805_);
v___y_786_ = v___y_797_;
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___y_801_;
v___y_790_ = v___y_802_;
v___y_791_ = v___y_803_;
v___y_792_ = v_ref_804_;
v___y_793_ = v_val_807_;
goto v___jp_785_;
}
}
v___jp_809_:
{
if (v___y_816_ == 0)
{
v___y_797_ = v___y_814_;
v___y_798_ = v___y_810_;
v___y_799_ = v___y_815_;
v___y_800_ = v___y_811_;
v___y_801_ = v___y_812_;
v___y_802_ = v___y_813_;
v___y_803_ = v_severity_719_;
goto v___jp_796_;
}
else
{
v___y_797_ = v___y_814_;
v___y_798_ = v___y_810_;
v___y_799_ = v___y_815_;
v___y_800_ = v___y_811_;
v___y_801_ = v___y_812_;
v___y_802_ = v___y_813_;
v___y_803_ = v___x_808_;
goto v___jp_796_;
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_object* v_fileName_819_; lean_object* v_fileMap_820_; lean_object* v_options_821_; lean_object* v_ref_822_; uint8_t v_suppressElabErrors_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___f_826_; uint8_t v___x_827_; uint8_t v___x_828_; 
v_fileName_819_ = lean_ctor_get(v___y_721_, 0);
v_fileMap_820_ = lean_ctor_get(v___y_721_, 1);
v_options_821_ = lean_ctor_get(v___y_721_, 2);
v_ref_822_ = lean_ctor_get(v___y_721_, 5);
v_suppressElabErrors_823_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*14 + 1);
v___x_824_ = lean_box(v___y_818_);
v___x_825_ = lean_box(v_suppressElabErrors_823_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_826_, 0, v___x_824_);
lean_closure_set(v___f_826_, 1, v___x_825_);
v___x_827_ = 1;
v___x_828_ = l_Lean_instBEqMessageSeverity_beq(v_severity_719_, v___x_827_);
if (v___x_828_ == 0)
{
lean_inc_ref(v_fileName_819_);
lean_inc_ref(v_fileMap_820_);
lean_inc(v_ref_822_);
v___y_810_ = v_suppressElabErrors_823_;
v___y_811_ = v_ref_822_;
v___y_812_ = v_fileMap_820_;
v___y_813_ = v_fileName_819_;
v___y_814_ = v___f_826_;
v___y_815_ = v___y_818_;
v___y_816_ = v___x_828_;
goto v___jp_809_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_warningAsError;
v___x_830_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_821_, v___x_829_);
lean_inc_ref(v_fileName_819_);
lean_inc_ref(v_fileMap_820_);
lean_inc(v_ref_822_);
v___y_810_ = v_suppressElabErrors_823_;
v___y_811_ = v_ref_822_;
v___y_812_ = v_fileMap_820_;
v___y_813_ = v_fileName_819_;
v___y_814_ = v___f_826_;
v___y_815_ = v___y_818_;
v___y_816_ = v___x_830_;
goto v___jp_809_;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v___y_721_);
lean_dec_ref(v_msgData_718_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_835_, lean_object* v_msgData_836_, lean_object* v_severity_837_, lean_object* v_isSilent_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v_severity_boxed_842_; uint8_t v_isSilent_boxed_843_; lean_object* v_res_844_; 
v_severity_boxed_842_ = lean_unbox(v_severity_837_);
v_isSilent_boxed_843_ = lean_unbox(v_isSilent_838_);
v_res_844_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_835_, v_msgData_836_, v_severity_boxed_842_, v_isSilent_boxed_843_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec(v_ref_835_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_845_, uint8_t v_severity_846_, uint8_t v_isSilent_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_ref_851_; lean_object* v___x_852_; 
v_ref_851_ = lean_ctor_get(v___y_848_, 5);
lean_inc(v_ref_851_);
v___x_852_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_851_, v_msgData_845_, v_severity_846_, v_isSilent_847_, v___y_848_, v___y_849_);
lean_dec(v_ref_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_853_, lean_object* v_severity_854_, lean_object* v_isSilent_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v_severity_boxed_859_; uint8_t v_isSilent_boxed_860_; lean_object* v_res_861_; 
v_severity_boxed_859_ = lean_unbox(v_severity_854_);
v_isSilent_boxed_860_ = lean_unbox(v_isSilent_855_);
v_res_861_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_853_, v_severity_boxed_859_, v_isSilent_boxed_860_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = 2;
v___x_867_ = 0;
v___x_868_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_862_, v___x_866_, v___x_867_, v___y_863_, v___y_864_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
return v_res_873_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v___x_886_; 
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v_id_880_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v_x_882_);
return v___x_886_;
}
else
{
lean_object* v_head_887_; lean_object* v_tail_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_945_; 
v_head_887_ = lean_ctor_get(v_x_881_, 0);
v_tail_888_ = lean_ctor_get(v_x_881_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_945_ == 0)
{
v___x_890_ = v_x_881_;
v_isShared_891_ = v_isSharedCheck_945_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_tail_888_);
lean_inc(v_head_887_);
lean_dec(v_x_881_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_945_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_fst_897_; lean_object* v___x_898_; lean_object* v_env_899_; uint8_t v___x_900_; uint8_t v___x_901_; 
v_fst_897_ = lean_ctor_get(v_head_887_, 0);
v___x_898_ = lean_st_ref_get(v___y_884_);
v_env_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_env_899_);
lean_dec(v___x_898_);
v___x_900_ = 1;
lean_inc(v_fst_897_);
v___x_901_ = l_Lean_Environment_contains(v_env_899_, v_fst_897_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v_fst_897_);
v___x_902_ = l_Lean_executeReservedNameAction(v_fst_897_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_903_; lean_object* v_env_904_; uint8_t v___x_905_; 
lean_dec_ref(v___x_902_);
v___x_903_ = lean_st_ref_get(v___y_884_);
v_env_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc_ref(v_env_904_);
lean_dec(v___x_903_);
v___x_905_ = l_Lean_Environment_containsOnBranch(v_env_904_, v_fst_897_);
if (v___x_905_ == 0)
{
lean_del_object(v___x_890_);
lean_dec(v_head_887_);
v_x_881_ = v_tail_888_;
goto _start;
}
else
{
goto v___jp_892_;
}
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_942_; 
lean_del_object(v___x_890_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_head_887_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_943_ = lean_ctor_get(v_head_887_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_head_887_, 0);
lean_dec(v_unused_944_);
v___x_908_ = v_head_887_;
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_head_887_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_941_; 
v_a_910_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_941_ == 0)
{
v___x_912_ = v___x_902_;
v_isShared_913_ = v_isSharedCheck_941_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_902_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_941_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___y_915_; uint8_t v___x_939_; 
v___x_939_ = l_Lean_Exception_isInterrupt(v_a_910_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; 
lean_inc(v_a_910_);
v___x_940_ = l_Lean_Exception_isRuntime(v_a_910_);
v___y_915_ = v___x_940_;
goto v___jp_914_;
}
else
{
v___y_915_ = v___x_939_;
goto v___jp_914_;
}
v___jp_914_:
{
if (v___y_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
lean_del_object(v___x_912_);
v___x_916_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_880_);
v___x_917_ = l_Lean_MessageData_ofName(v_id_880_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 7);
lean_ctor_set(v___x_908_, 1, v___x_917_);
lean_ctor_set(v___x_908_, 0, v___x_916_);
v___x_919_ = v___x_908_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_935_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_920_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_Exception_toMessageData(v_a_910_);
v___x_923_ = l_Lean_indentD(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_inc_ref(v___y_883_);
v___x_925_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_924_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref(v___x_925_);
v_x_881_ = v_tail_888_;
goto _start;
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_tail_888_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v_x_882_);
lean_dec(v_id_880_);
v_a_927_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
else
{
lean_object* v___x_937_; 
lean_del_object(v___x_908_);
lean_dec(v_tail_888_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v_x_882_);
lean_dec(v_id_880_);
if (v_isShared_913_ == 0)
{
v___x_937_ = v___x_912_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_910_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
}
else
{
goto v___jp_892_;
}
v___jp_892_:
{
lean_object* v___x_894_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_x_882_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_head_887_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_x_882_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
v_x_881_ = v_tail_888_;
v_x_882_ = v___x_894_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_946_, v_x_947_, v_x_948_, v___y_949_, v___y_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(lean_object* v_msgData_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = 1;
v___x_958_ = 0;
v___x_959_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_953_, v___x_957_, v___x_958_, v___y_954_, v___y_955_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v_msgData_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(lean_object* v_opt_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_options_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_options_968_ = lean_ctor_get(v___y_966_, 2);
v___x_969_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__3(v_options_968_, v_opt_965_);
v___x_970_ = lean_box(v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_opt_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_972_, v___y_973_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_opt_972_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_id_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_env_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1009_; 
v___x_986_ = lean_st_ref_get(v___y_984_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v___x_988_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_989_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v___x_988_, v___y_983_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v_isExporting_999_; 
v_isExporting_999_ = lean_ctor_get_uint8(v_env_987_, sizeof(void*)*8);
lean_dec_ref(v_env_987_);
if (v_isExporting_999_ == 0)
{
lean_dec(v_a_990_);
lean_dec_ref(v___y_983_);
lean_dec(v_id_982_);
goto v___jp_994_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = l_Lean_isPrivateName(v_id_982_);
if (v___x_1000_ == 0)
{
lean_dec(v_a_990_);
lean_dec_ref(v___y_983_);
lean_dec(v_id_982_);
goto v___jp_994_;
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v___y_983_);
lean_dec(v_id_982_);
goto v___jp_994_;
}
else
{
lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_992_);
v___x_1002_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1);
v___x_1003_ = 0;
v___x_1004_ = l_Lean_MessageData_ofConstName(v_id_982_, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v___x_1007_, v___y_983_, v___y_984_);
return v___x_1008_;
}
}
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_id_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_id_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(lean_object* v_x_1015_){
_start:
{
lean_object* v_fst_1016_; uint8_t v___x_1017_; 
v_fst_1016_ = lean_ctor_get(v_x_1015_, 0);
v___x_1017_ = l_Lean_isPrivateName(v_fst_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0___boxed(lean_object* v_x_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(v_x_1018_);
lean_dec_ref(v_x_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_1022_, uint8_t v_enableLog_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v_env_1028_; lean_object* v_options_1029_; lean_object* v_currNamespace_1030_; lean_object* v_openDecls_1031_; lean_object* v___x_1032_; lean_object* v_env_1033_; lean_object* v_res_1034_; 
v___x_1027_ = lean_st_ref_get(v___y_1025_);
v_env_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref(v_env_1028_);
lean_dec(v___x_1027_);
v_options_1029_ = lean_ctor_get(v___y_1024_, 2);
v_currNamespace_1030_ = lean_ctor_get(v___y_1024_, 6);
v_openDecls_1031_ = lean_ctor_get(v___y_1024_, 7);
v___x_1032_ = lean_st_ref_get(v___y_1025_);
v_env_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1033_);
lean_dec(v___x_1032_);
lean_inc(v_openDecls_1031_);
lean_inc(v_currNamespace_1030_);
v_res_1034_ = l_Lean_ResolveName_resolveGlobalName(v_env_1028_, v_options_1029_, v_currNamespace_1030_, v_openDecls_1031_, v_id_1022_);
if (v_enableLog_1023_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_env_1033_);
lean_dec_ref(v___y_1024_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_res_1034_);
return v___x_1035_;
}
else
{
uint8_t v_isExporting_1036_; 
v_isExporting_1036_ = lean_ctor_get_uint8(v_env_1033_, sizeof(void*)*8);
lean_dec_ref(v_env_1033_);
if (v_isExporting_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v___y_1024_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_res_1034_);
return v___x_1037_;
}
else
{
lean_object* v___f_1038_; lean_object* v___x_1039_; 
v___f_1038_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0));
lean_inc(v_res_1034_);
v___x_1039_ = l_List_find_x3f___redArg(v___f_1038_, v_res_1034_);
if (lean_obj_tag(v___x_1039_) == 1)
{
lean_object* v_val_1040_; lean_object* v_fst_1041_; lean_object* v___x_1042_; 
v_val_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v___x_1039_);
v_fst_1041_ = lean_ctor_get(v_val_1040_, 0);
lean_inc(v_fst_1041_);
lean_dec(v_val_1040_);
v___x_1042_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_fst_1041_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v___x_1042_, 0);
lean_dec(v_unused_1050_);
v___x_1044_ = v___x_1042_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v___x_1042_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_res_1034_);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_res_1034_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_res_1034_);
v_a_1051_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1042_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v___x_1059_; 
lean_dec(v___x_1039_);
lean_dec_ref(v___y_1024_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_res_1034_);
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_1060_, lean_object* v_enableLog_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_enableLog_boxed_1065_; lean_object* v_res_1066_; 
v_enableLog_boxed_1065_ = lean_unbox(v_enableLog_1061_);
v_res_1066_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1060_, v_enableLog_boxed_1065_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
uint8_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = 1;
lean_inc_ref(v_a_1068_);
lean_inc(v_id_1067_);
v___x_1072_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1067_, v___x_1071_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1067_, v_a_1073_, v___x_1074_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_List_reverse___redArg(v_a_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
return v___x_1075_;
}
}
else
{
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_id_1067_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_realizeGlobalName(v_id_1085_, v_a_1086_, v_a_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(lean_object* v_opt_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_1090_, v___y_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___boxed(lean_object* v_opt_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(v_opt_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v_opt_1095_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
if (lean_obj_tag(v_a_1100_) == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = l_List_reverse___redArg(v_a_1101_);
return v___x_1102_;
}
else
{
lean_object* v_head_1103_; lean_object* v_tail_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1113_; 
v_head_1103_ = lean_ctor_get(v_a_1100_, 0);
v_tail_1104_ = lean_ctor_get(v_a_1100_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_1100_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1106_ = v_a_1100_;
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_tail_1104_);
lean_inc(v_head_1103_);
lean_dec(v_a_1100_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_fst_1108_; lean_object* v___x_1110_; 
v_fst_1108_ = lean_ctor_get(v_head_1103_, 0);
lean_inc(v_fst_1108_);
lean_dec(v_head_1103_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v_a_1101_);
lean_ctor_set(v___x_1106_, 0, v_fst_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1108_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_a_1101_);
v___x_1110_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v_a_1100_ = v_tail_1104_;
v_a_1101_ = v___x_1110_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_ref_1118_; lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_ref_1118_ = lean_ctor_get(v___y_1115_, 5);
v___x_1119_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7(v_msg_1114_, v___y_1115_, v___y_1116_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_ref_1118_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_ref_1118_);
lean_ctor_set(v___x_1124_, 1, v_a_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_fileName_1139_; lean_object* v_fileMap_1140_; lean_object* v_options_1141_; lean_object* v_currRecDepth_1142_; lean_object* v_maxRecDepth_1143_; lean_object* v_ref_1144_; lean_object* v_currNamespace_1145_; lean_object* v_openDecls_1146_; lean_object* v_initHeartbeats_1147_; lean_object* v_maxHeartbeats_1148_; lean_object* v_quotContext_1149_; lean_object* v_currMacroScope_1150_; uint8_t v_diag_1151_; lean_object* v_cancelTk_x3f_1152_; uint8_t v_suppressElabErrors_1153_; lean_object* v_inheritedTraceOptions_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v_fileName_1139_ = lean_ctor_get(v___y_1136_, 0);
v_fileMap_1140_ = lean_ctor_get(v___y_1136_, 1);
v_options_1141_ = lean_ctor_get(v___y_1136_, 2);
v_currRecDepth_1142_ = lean_ctor_get(v___y_1136_, 3);
v_maxRecDepth_1143_ = lean_ctor_get(v___y_1136_, 4);
v_ref_1144_ = lean_ctor_get(v___y_1136_, 5);
v_currNamespace_1145_ = lean_ctor_get(v___y_1136_, 6);
v_openDecls_1146_ = lean_ctor_get(v___y_1136_, 7);
v_initHeartbeats_1147_ = lean_ctor_get(v___y_1136_, 8);
v_maxHeartbeats_1148_ = lean_ctor_get(v___y_1136_, 9);
v_quotContext_1149_ = lean_ctor_get(v___y_1136_, 10);
v_currMacroScope_1150_ = lean_ctor_get(v___y_1136_, 11);
v_diag_1151_ = lean_ctor_get_uint8(v___y_1136_, sizeof(void*)*14);
v_cancelTk_x3f_1152_ = lean_ctor_get(v___y_1136_, 12);
v_suppressElabErrors_1153_ = lean_ctor_get_uint8(v___y_1136_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1154_ = lean_ctor_get(v___y_1136_, 13);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___y_1136_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v___y_1136_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_inheritedTraceOptions_1154_);
lean_inc(v_cancelTk_x3f_1152_);
lean_inc(v_currMacroScope_1150_);
lean_inc(v_quotContext_1149_);
lean_inc(v_maxHeartbeats_1148_);
lean_inc(v_initHeartbeats_1147_);
lean_inc(v_openDecls_1146_);
lean_inc(v_currNamespace_1145_);
lean_inc(v_ref_1144_);
lean_inc(v_maxRecDepth_1143_);
lean_inc(v_currRecDepth_1142_);
lean_inc(v_options_1141_);
lean_inc(v_fileMap_1140_);
lean_inc(v_fileName_1139_);
lean_dec(v___y_1136_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_ref_1158_; lean_object* v___x_1160_; 
v_ref_1158_ = l_Lean_replaceRef(v_ref_1134_, v_ref_1144_);
lean_dec(v_ref_1144_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 5, v_ref_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fileName_1139_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_fileMap_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_options_1141_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_currRecDepth_1142_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_maxRecDepth_1143_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_ref_1158_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_currNamespace_1145_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_openDecls_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_initHeartbeats_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_maxHeartbeats_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 10, v_quotContext_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 11, v_currMacroScope_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 12, v_cancelTk_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 13, v_inheritedTraceOptions_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*14, v_diag_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*14 + 1, v_suppressElabErrors_1153_);
v___x_1160_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1135_, v___x_1160_, v___y_1137_);
lean_dec_ref(v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1164_, v_msg_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec(v_ref_1164_);
return v_res_1169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1181_ = l_Lean_stringToMessageData(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1184_ = l_Lean_stringToMessageData(v___x_1183_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1187_ = l_Lean_stringToMessageData(v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1190_ = l_Lean_stringToMessageData(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1191_, lean_object* v_declHint_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = l_Lean_Name_isAnonymous(v_declHint_1192_);
if (v___x_1197_ == 0)
{
uint8_t v_isExporting_1198_; 
v_isExporting_1198_ = lean_ctor_get_uint8(v_env_1196_, sizeof(void*)*8);
if (v_isExporting_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_env_1196_);
lean_dec(v_declHint_1192_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_msg_1191_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
lean_inc_ref(v_env_1196_);
v___x_1200_ = l_Lean_Environment_setExporting(v_env_1196_, v___x_1197_);
lean_inc(v_declHint_1192_);
lean_inc_ref(v___x_1200_);
v___x_1201_ = l_Lean_Environment_contains(v___x_1200_, v_declHint_1192_, v_isExporting_1198_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_env_1196_);
lean_dec(v_declHint_1192_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_msg_1191_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_c_1208_; lean_object* v___x_1209_; 
v___x_1203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__2);
v___x_1204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__4_spec__5_spec__7___closed__5);
v___x_1205_ = l_Lean_Options_empty;
v___x_1206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1200_);
lean_ctor_set(v___x_1206_, 1, v___x_1203_);
lean_ctor_set(v___x_1206_, 2, v___x_1204_);
lean_ctor_set(v___x_1206_, 3, v___x_1205_);
lean_inc(v_declHint_1192_);
v___x_1207_ = l_Lean_MessageData_ofConstName(v_declHint_1192_, v___x_1197_);
v_c_1208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1208_, 0, v___x_1206_);
lean_ctor_set(v_c_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1196_, v_declHint_1192_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_env_1196_);
lean_dec(v_declHint_1192_);
v___x_1210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_c_1208_);
v___x_1212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_MessageData_note(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_msg_1191_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1252_; 
v_val_1217_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1219_ = v___x_1209_;
v_isShared_1220_ = v_isSharedCheck_1252_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_dec(v___x_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1252_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_mod_1224_; uint8_t v___x_1225_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_Environment_header(v_env_1196_);
lean_dec_ref(v_env_1196_);
v___x_1223_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1222_);
v_mod_1224_ = lean_array_get(v___x_1221_, v___x_1223_, v_val_1217_);
lean_dec(v_val_1217_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = l_Lean_isPrivateName(v_declHint_1192_);
lean_dec(v_declHint_1192_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_c_1208_);
v___x_1228_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_MessageData_ofName(v_mod_1224_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_MessageData_note(v___x_1233_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_msg_1191_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1235_);
v___x_1237_ = v___x_1219_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_c_1208_);
v___x_1241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_MessageData_ofName(v_mod_1224_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_MessageData_note(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_msg_1191_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1248_);
v___x_1250_ = v___x_1219_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1253_; 
lean_dec_ref(v_env_1196_);
lean_dec(v_declHint_1192_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_msg_1191_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1254_, lean_object* v_declHint_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1254_, v_declHint_1255_, v___y_1256_);
lean_dec(v___y_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1259_, lean_object* v_declHint_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1274_; 
v___x_1264_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1259_, v_declHint_1260_, v___y_1262_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1269_ = l_Lean_unknownIdentifierMessageTag;
v___x_1270_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1275_, v_declHint_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1281_, lean_object* v_msg_1282_, lean_object* v_declHint_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_a_1288_; lean_object* v___x_1289_; 
v___x_1287_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1282_, v_declHint_1283_, v___y_1284_, v___y_1285_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1281_, v_a_1288_, v___y_1284_, v___y_1285_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1290_, lean_object* v_msg_1291_, lean_object* v_declHint_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1290_, v_msg_1291_, v_declHint_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec(v_ref_1290_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1303_, lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1308_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1309_ = 0;
lean_inc(v_constName_1304_);
v___x_1310_ = l_Lean_MessageData_ofConstName(v_constName_1304_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1303_, v___x_1313_, v_constName_1304_, v___y_1305_, v___y_1306_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1315_, lean_object* v_constName_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1315_, v_constName_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec(v_ref_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
if (lean_obj_tag(v_a_1321_) == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = l_List_reverse___redArg(v_a_1322_);
return v___x_1323_;
}
else
{
lean_object* v_head_1324_; lean_object* v_tail_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1336_; 
v_head_1324_ = lean_ctor_get(v_a_1321_, 0);
v_tail_1325_ = lean_ctor_get(v_a_1321_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1321_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1327_ = v_a_1321_;
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_tail_1325_);
lean_inc(v_head_1324_);
lean_dec(v_a_1321_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_snd_1329_; uint8_t v___x_1330_; 
v_snd_1329_ = lean_ctor_get(v_head_1324_, 1);
v___x_1330_ = l_List_isEmpty___redArg(v_snd_1329_);
if (v___x_1330_ == 0)
{
lean_del_object(v___x_1327_);
lean_dec(v_head_1324_);
v_a_1321_ = v_tail_1325_;
goto _start;
}
else
{
lean_object* v___x_1333_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_a_1322_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_head_1324_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_a_1322_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
v_a_1321_ = v_tail_1325_;
v_a_1322_ = v___x_1333_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1337_, lean_object* v_cs_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v_cs_1343_; uint8_t v___x_1347_; 
v___x_1342_ = lean_box(0);
v_cs_1343_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1338_, v___x_1342_);
v___x_1347_ = l_List_isEmpty___redArg(v_cs_1343_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v___y_1339_);
lean_dec(v_n_1337_);
goto v___jp_1344_;
}
else
{
lean_object* v_ref_1348_; lean_object* v___x_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_cs_1343_);
v_ref_1348_ = lean_ctor_get(v___y_1339_, 5);
lean_inc(v_ref_1348_);
v___x_1349_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1348_, v_n_1337_, v___y_1339_, v___y_1340_);
lean_dec(v_ref_1348_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
v___jp_1344_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1343_, v___x_1342_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1358_, lean_object* v_cs_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1358_, v_cs_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; 
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_n_1364_);
v___x_1368_ = l_Lean_realizeGlobalName(v_n_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1364_, v_a_1369_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
return v___x_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_n_1364_);
v_a_1371_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1368_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_realizeGlobalConstCore(v_n_1379_, v_a_1380_, v_a_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1385_, v_constName_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_ref_1392_, lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1391_, v_ref_1392_, v_constName_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec(v_ref_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1398_, lean_object* v_ref_1399_, lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1399_, v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1406_, v_ref_1407_, v_msg_1408_, v_declHint_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v_ref_1407_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1414_, v_declHint_1415_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1420_, lean_object* v_declHint_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1420_, v_declHint_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1427_, v_msg_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_ref_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1433_, v_ref_1434_, v_msg_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec(v_ref_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1446_, v_msg_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
if (lean_obj_tag(v_a_1452_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l_List_reverse___redArg(v_a_1453_);
return v___x_1454_;
}
else
{
lean_object* v_head_1455_; lean_object* v_tail_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1465_; 
v_head_1455_ = lean_ctor_get(v_a_1452_, 0);
v_tail_1456_ = lean_ctor_get(v_a_1452_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1452_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1458_ = v_a_1452_;
v_isShared_1459_ = v_isSharedCheck_1465_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_tail_1456_);
lean_inc(v_head_1455_);
lean_dec(v_a_1452_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1465_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = l_Lean_MessageData_ofExpr(v_head_1455_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v_a_1453_);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_a_1453_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
v_a_1452_ = v_tail_1456_;
v_a_1453_ = v___x_1462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = l_List_reverse___redArg(v_a_1467_);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_head_1469_ = lean_ctor_get(v_a_1466_, 0);
v_tail_1470_ = lean_ctor_get(v_a_1466_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v_a_1466_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_tail_1470_);
lean_inc(v_head_1469_);
lean_dec(v_a_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Lean_mkConst(v_head_1469_, v___x_1474_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v_a_1467_);
lean_ctor_set(v___x_1472_, 0, v___x_1475_);
v___x_1477_ = v___x_1472_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1467_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v_a_1466_ = v_tail_1470_;
v_a_1467_ = v___x_1477_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1487_, lean_object* v_cs_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
if (lean_obj_tag(v_cs_1488_) == 1)
{
lean_object* v_tail_1504_; 
v_tail_1504_ = lean_ctor_get(v_cs_1488_, 1);
if (lean_obj_tag(v_tail_1504_) == 0)
{
lean_object* v_head_1505_; lean_object* v___x_1506_; 
lean_dec(v_n_1487_);
v_head_1505_ = lean_ctor_get(v_cs_1488_, 0);
lean_inc(v_head_1505_);
lean_dec_ref(v_cs_1488_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_head_1505_);
return v___x_1506_;
}
else
{
goto v___jp_1492_;
}
}
else
{
goto v___jp_1492_;
}
v___jp_1492_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1493_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1494_ = l_Lean_MessageData_ofName(v_n_1487_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_box(0);
v___x_1499_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1488_, v___x_1498_);
v___x_1500_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1499_, v___x_1498_);
v___x_1501_ = l_Lean_MessageData_ofList(v___x_1500_);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1497_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1502_, v___y_1489_, v___y_1490_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1507_, lean_object* v_cs_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1507_, v_cs_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; 
lean_inc(v_a_1515_);
lean_inc_ref(v_a_1514_);
lean_inc(v_n_1513_);
v___x_1517_ = l_Lean_realizeGlobalConstCore(v_n_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1513_, v_a_1518_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_n_1513_);
v_a_1520_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1517_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1517_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1528_, v_a_1529_, v_a_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
if (lean_obj_tag(v_a_1533_) == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_to_list(v_a_1534_);
return v___x_1535_;
}
else
{
lean_object* v_head_1536_; 
v_head_1536_ = lean_ctor_get(v_a_1533_, 0);
if (lean_obj_tag(v_head_1536_) == 1)
{
lean_object* v_fields_1537_; 
v_fields_1537_ = lean_ctor_get(v_head_1536_, 1);
if (lean_obj_tag(v_fields_1537_) == 0)
{
lean_object* v_tail_1538_; lean_object* v_n_1539_; lean_object* v___x_1540_; 
lean_inc_ref(v_head_1536_);
v_tail_1538_ = lean_ctor_get(v_a_1533_, 1);
lean_inc(v_tail_1538_);
lean_dec_ref(v_a_1533_);
v_n_1539_ = lean_ctor_get(v_head_1536_, 0);
lean_inc(v_n_1539_);
lean_dec_ref(v_head_1536_);
v___x_1540_ = lean_array_push(v_a_1534_, v_n_1539_);
v_a_1533_ = v_tail_1538_;
v_a_1534_ = v___x_1540_;
goto _start;
}
else
{
lean_object* v_tail_1542_; 
v_tail_1542_ = lean_ctor_get(v_a_1533_, 1);
lean_inc(v_tail_1542_);
lean_dec_ref(v_a_1533_);
v_a_1533_ = v_tail_1542_;
goto _start;
}
}
else
{
lean_object* v_tail_1544_; 
v_tail_1544_ = lean_ctor_get(v_a_1533_, 1);
lean_inc(v_tail_1544_);
lean_dec_ref(v_a_1533_);
v_a_1533_ = v_tail_1544_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1552_ = l_Lean_MessageData_ofFormat(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1553_, lean_object* v_k_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
if (lean_obj_tag(v_stx_1553_) == 3)
{
lean_object* v_val_1558_; lean_object* v_preresolved_1559_; lean_object* v___x_1560_; lean_object* v_pre_1561_; uint8_t v___x_1562_; 
v_val_1558_ = lean_ctor_get(v_stx_1553_, 2);
lean_inc(v_val_1558_);
v_preresolved_1559_ = lean_ctor_get(v_stx_1553_, 3);
v___x_1560_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1559_);
v_pre_1561_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1559_, v___x_1560_);
v___x_1562_ = l_List_isEmpty___redArg(v_pre_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec(v_val_1558_);
lean_dec_ref(v_stx_1553_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec_ref(v_k_1554_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_pre_1561_);
return v___x_1563_;
}
else
{
lean_object* v_fileName_1564_; lean_object* v_fileMap_1565_; lean_object* v_options_1566_; lean_object* v_currRecDepth_1567_; lean_object* v_maxRecDepth_1568_; lean_object* v_ref_1569_; lean_object* v_currNamespace_1570_; lean_object* v_openDecls_1571_; lean_object* v_initHeartbeats_1572_; lean_object* v_maxHeartbeats_1573_; lean_object* v_quotContext_1574_; lean_object* v_currMacroScope_1575_; uint8_t v_diag_1576_; lean_object* v_cancelTk_x3f_1577_; uint8_t v_suppressElabErrors_1578_; lean_object* v_inheritedTraceOptions_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_pre_1561_);
v_fileName_1564_ = lean_ctor_get(v___y_1555_, 0);
v_fileMap_1565_ = lean_ctor_get(v___y_1555_, 1);
v_options_1566_ = lean_ctor_get(v___y_1555_, 2);
v_currRecDepth_1567_ = lean_ctor_get(v___y_1555_, 3);
v_maxRecDepth_1568_ = lean_ctor_get(v___y_1555_, 4);
v_ref_1569_ = lean_ctor_get(v___y_1555_, 5);
v_currNamespace_1570_ = lean_ctor_get(v___y_1555_, 6);
v_openDecls_1571_ = lean_ctor_get(v___y_1555_, 7);
v_initHeartbeats_1572_ = lean_ctor_get(v___y_1555_, 8);
v_maxHeartbeats_1573_ = lean_ctor_get(v___y_1555_, 9);
v_quotContext_1574_ = lean_ctor_get(v___y_1555_, 10);
v_currMacroScope_1575_ = lean_ctor_get(v___y_1555_, 11);
v_diag_1576_ = lean_ctor_get_uint8(v___y_1555_, sizeof(void*)*14);
v_cancelTk_x3f_1577_ = lean_ctor_get(v___y_1555_, 12);
v_suppressElabErrors_1578_ = lean_ctor_get_uint8(v___y_1555_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1579_ = lean_ctor_get(v___y_1555_, 13);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___y_1555_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1581_ = v___y_1555_;
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_inheritedTraceOptions_1579_);
lean_inc(v_cancelTk_x3f_1577_);
lean_inc(v_currMacroScope_1575_);
lean_inc(v_quotContext_1574_);
lean_inc(v_maxHeartbeats_1573_);
lean_inc(v_initHeartbeats_1572_);
lean_inc(v_openDecls_1571_);
lean_inc(v_currNamespace_1570_);
lean_inc(v_ref_1569_);
lean_inc(v_maxRecDepth_1568_);
lean_inc(v_currRecDepth_1567_);
lean_inc(v_options_1566_);
lean_inc(v_fileMap_1565_);
lean_inc(v_fileName_1564_);
lean_dec(v___y_1555_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1588_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_ref_1583_; lean_object* v___x_1585_; 
v_ref_1583_ = l_Lean_replaceRef(v_stx_1553_, v_ref_1569_);
lean_dec(v_ref_1569_);
lean_dec_ref(v_stx_1553_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 5, v_ref_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_fileName_1564_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_fileMap_1565_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_options_1566_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_currRecDepth_1567_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_maxRecDepth_1568_);
lean_ctor_set(v_reuseFailAlloc_1587_, 5, v_ref_1583_);
lean_ctor_set(v_reuseFailAlloc_1587_, 6, v_currNamespace_1570_);
lean_ctor_set(v_reuseFailAlloc_1587_, 7, v_openDecls_1571_);
lean_ctor_set(v_reuseFailAlloc_1587_, 8, v_initHeartbeats_1572_);
lean_ctor_set(v_reuseFailAlloc_1587_, 9, v_maxHeartbeats_1573_);
lean_ctor_set(v_reuseFailAlloc_1587_, 10, v_quotContext_1574_);
lean_ctor_set(v_reuseFailAlloc_1587_, 11, v_currMacroScope_1575_);
lean_ctor_set(v_reuseFailAlloc_1587_, 12, v_cancelTk_x3f_1577_);
lean_ctor_set(v_reuseFailAlloc_1587_, 13, v_inheritedTraceOptions_1579_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*14, v_diag_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*14 + 1, v_suppressElabErrors_1578_);
v___x_1585_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_apply_4(v_k_1554_, v_val_1558_, v___x_1585_, v___y_1556_, lean_box(0));
return v___x_1586_;
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v_k_1554_);
v___x_1589_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1590_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1553_, v___x_1589_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec(v_stx_1553_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1591_, lean_object* v_k_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1591_, v_k_1592_, v___y_1593_, v___y_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_fileName_1602_; lean_object* v_fileMap_1603_; lean_object* v_options_1604_; lean_object* v_currRecDepth_1605_; lean_object* v_maxRecDepth_1606_; lean_object* v_ref_1607_; lean_object* v_currNamespace_1608_; lean_object* v_openDecls_1609_; lean_object* v_initHeartbeats_1610_; lean_object* v_maxHeartbeats_1611_; lean_object* v_quotContext_1612_; lean_object* v_currMacroScope_1613_; uint8_t v_diag_1614_; lean_object* v_cancelTk_x3f_1615_; uint8_t v_suppressElabErrors_1616_; lean_object* v_inheritedTraceOptions_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1627_; 
v_fileName_1602_ = lean_ctor_get(v_a_1599_, 0);
v_fileMap_1603_ = lean_ctor_get(v_a_1599_, 1);
v_options_1604_ = lean_ctor_get(v_a_1599_, 2);
v_currRecDepth_1605_ = lean_ctor_get(v_a_1599_, 3);
v_maxRecDepth_1606_ = lean_ctor_get(v_a_1599_, 4);
v_ref_1607_ = lean_ctor_get(v_a_1599_, 5);
v_currNamespace_1608_ = lean_ctor_get(v_a_1599_, 6);
v_openDecls_1609_ = lean_ctor_get(v_a_1599_, 7);
v_initHeartbeats_1610_ = lean_ctor_get(v_a_1599_, 8);
v_maxHeartbeats_1611_ = lean_ctor_get(v_a_1599_, 9);
v_quotContext_1612_ = lean_ctor_get(v_a_1599_, 10);
v_currMacroScope_1613_ = lean_ctor_get(v_a_1599_, 11);
v_diag_1614_ = lean_ctor_get_uint8(v_a_1599_, sizeof(void*)*14);
v_cancelTk_x3f_1615_ = lean_ctor_get(v_a_1599_, 12);
v_suppressElabErrors_1616_ = lean_ctor_get_uint8(v_a_1599_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1617_ = lean_ctor_get(v_a_1599_, 13);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1619_ = v_a_1599_;
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_inheritedTraceOptions_1617_);
lean_inc(v_cancelTk_x3f_1615_);
lean_inc(v_currMacroScope_1613_);
lean_inc(v_quotContext_1612_);
lean_inc(v_maxHeartbeats_1611_);
lean_inc(v_initHeartbeats_1610_);
lean_inc(v_openDecls_1609_);
lean_inc(v_currNamespace_1608_);
lean_inc(v_ref_1607_);
lean_inc(v_maxRecDepth_1606_);
lean_inc(v_currRecDepth_1605_);
lean_inc(v_options_1604_);
lean_inc(v_fileMap_1603_);
lean_inc(v_fileName_1602_);
lean_dec(v_a_1599_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v_ref_1622_; lean_object* v___x_1624_; 
v___x_1621_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1622_ = l_Lean_replaceRef(v_stx_1598_, v_ref_1607_);
lean_dec(v_ref_1607_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 5, v_ref_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_fileName_1602_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_fileMap_1603_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_options_1604_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_currRecDepth_1605_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_maxRecDepth_1606_);
lean_ctor_set(v_reuseFailAlloc_1626_, 5, v_ref_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 6, v_currNamespace_1608_);
lean_ctor_set(v_reuseFailAlloc_1626_, 7, v_openDecls_1609_);
lean_ctor_set(v_reuseFailAlloc_1626_, 8, v_initHeartbeats_1610_);
lean_ctor_set(v_reuseFailAlloc_1626_, 9, v_maxHeartbeats_1611_);
lean_ctor_set(v_reuseFailAlloc_1626_, 10, v_quotContext_1612_);
lean_ctor_set(v_reuseFailAlloc_1626_, 11, v_currMacroScope_1613_);
lean_ctor_set(v_reuseFailAlloc_1626_, 12, v_cancelTk_x3f_1615_);
lean_ctor_set(v_reuseFailAlloc_1626_, 13, v_inheritedTraceOptions_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*14, v_diag_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*14 + 1, v_suppressElabErrors_1616_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1598_, v___x_1621_, v___x_1624_, v_a_1600_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_realizeGlobalConst(v_stx_1628_, v_a_1629_, v_a_1630_);
return v_res_1632_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_toApplicative_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1673_; 
v___x_1640_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1641_ = l_ReaderT_instMonad___redArg(v___x_1640_);
v_toApplicative_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1641_, 1);
lean_dec(v_unused_1674_);
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1673_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_toApplicative_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1673_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_toFunctor_1646_; lean_object* v_toSeq_1647_; lean_object* v_toSeqLeft_1648_; lean_object* v_toSeqRight_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1671_; 
v_toFunctor_1646_ = lean_ctor_get(v_toApplicative_1642_, 0);
v_toSeq_1647_ = lean_ctor_get(v_toApplicative_1642_, 2);
v_toSeqLeft_1648_ = lean_ctor_get(v_toApplicative_1642_, 3);
v_toSeqRight_1649_ = lean_ctor_get(v_toApplicative_1642_, 4);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_toApplicative_1642_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_toApplicative_1642_, 1);
lean_dec(v_unused_1672_);
v___x_1651_ = v_toApplicative_1642_;
v_isShared_1652_ = v_isSharedCheck_1671_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_toSeqRight_1649_);
lean_inc(v_toSeqLeft_1648_);
lean_inc(v_toSeq_1647_);
lean_inc(v_toFunctor_1646_);
lean_dec(v_toApplicative_1642_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1671_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; lean_object* v___f_1659_; lean_object* v___f_1660_; lean_object* v___x_1662_; 
v___f_1653_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1654_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1646_);
v___f_1655_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1655_, 0, v_toFunctor_1646_);
v___f_1656_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1656_, 0, v_toFunctor_1646_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___f_1655_);
lean_ctor_set(v___x_1657_, 1, v___f_1656_);
v___f_1658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1658_, 0, v_toSeqRight_1649_);
v___f_1659_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1659_, 0, v_toSeqLeft_1648_);
v___f_1660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1660_, 0, v_toSeq_1647_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v___f_1658_);
lean_ctor_set(v___x_1651_, 3, v___f_1659_);
lean_ctor_set(v___x_1651_, 2, v___f_1660_);
lean_ctor_set(v___x_1651_, 1, v___f_1653_);
lean_ctor_set(v___x_1651_, 0, v___x_1657_);
v___x_1662_ = v___x_1651_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___f_1653_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v___f_1660_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___f_1659_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___f_1658_);
v___x_1662_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___f_1654_);
lean_ctor_set(v___x_1644_, 0, v___x_1662_);
v___x_1664_ = v___x_1644_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___f_1654_);
v___x_1664_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_197__overap_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = l_instInhabitedOfMonad___redArg(v___x_1664_, v___x_1665_);
v___x_197__overap_1667_ = lean_panic_fn(v___x_1666_, v_msg_1636_);
v___x_1668_ = lean_apply_3(v___x_197__overap_1667_, v___y_1637_, v___y_1638_, lean_box(0));
return v___x_1668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1675_, v___y_1676_, v___y_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
return v_x_1681_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_head_1683_ = lean_ctor_get(v_x_1682_, 0);
v_tail_1684_ = lean_ctor_get(v_x_1682_, 1);
v___x_1685_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1686_ = lean_string_append(v_x_1681_, v___x_1685_);
v___x_1687_ = lean_expr_dbg_to_string(v_head_1683_);
v___x_1688_ = lean_string_append(v___x_1686_, v___x_1687_);
lean_dec_ref(v___x_1687_);
v_x_1681_ = v___x_1688_;
v_x_1682_ = v_tail_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1690_, v_x_1691_);
lean_dec(v_x_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1697_;
}
else
{
lean_object* v_tail_1698_; 
v_tail_1698_ = lean_ctor_get(v_x_1696_, 1);
if (lean_obj_tag(v_tail_1698_) == 0)
{
lean_object* v_head_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_head_1699_ = lean_ctor_get(v_x_1696_, 0);
v___x_1700_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1701_ = lean_expr_dbg_to_string(v_head_1699_);
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1704_ = lean_string_append(v___x_1702_, v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v_head_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint32_t v___x_1710_; lean_object* v___x_1711_; 
v_head_1705_ = lean_ctor_get(v_x_1696_, 0);
v___x_1706_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1707_ = lean_expr_dbg_to_string(v_head_1705_);
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1708_, v_tail_1698_);
v___x_1710_ = 93;
v___x_1711_ = lean_string_push(v___x_1709_, v___x_1710_);
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1712_);
lean_dec(v_x_1712_);
return v_res_1713_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1717_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1718_ = lean_unsigned_to_nat(11u);
v___x_1719_ = lean_unsigned_to_nat(429u);
v___x_1720_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1721_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1722_ = l_mkPanicMessageWithDecl(v___x_1721_, v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1725_, lean_object* v_cs_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
if (lean_obj_tag(v_cs_1726_) == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_id_1725_);
v___x_1730_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1731_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1730_, v___y_1727_, v___y_1728_);
return v___x_1731_;
}
else
{
lean_object* v_tail_1732_; 
v_tail_1732_ = lean_ctor_get(v_cs_1726_, 1);
if (lean_obj_tag(v_tail_1732_) == 0)
{
lean_object* v_head_1733_; lean_object* v___x_1734_; 
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v_id_1725_);
v_head_1733_ = lean_ctor_get(v_cs_1726_, 0);
lean_inc(v_head_1733_);
lean_dec_ref(v_cs_1726_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_head_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1735_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1736_ = lean_box(0);
v___x_1737_ = 0;
lean_inc(v_id_1725_);
v___x_1738_ = l_Lean_Syntax_formatStx(v_id_1725_, v___x_1736_, v___x_1737_);
v___x_1739_ = l_Std_Format_defWidth;
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = l_Std_Format_pretty(v___x_1738_, v___x_1739_, v___x_1740_, v___x_1740_);
v___x_1742_ = lean_string_append(v___x_1735_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
v___x_1745_ = lean_box(0);
v___x_1746_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1726_, v___x_1745_);
v___x_1747_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1746_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_string_append(v___x_1744_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
v___x_1750_ = l_Lean_MessageData_ofFormat(v___x_1749_);
v___x_1751_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1725_, v___x_1750_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec(v_id_1725_);
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1752_, lean_object* v_cs_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1752_, v_cs_1753_, v___y_1754_, v___y_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
lean_inc(v_a_1760_);
lean_inc_ref(v_a_1759_);
lean_inc(v_id_1758_);
v___x_1762_ = l_Lean_realizeGlobalConst(v_id_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1758_, v_a_1763_, v_a_1759_, v_a_1760_);
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_id_1758_);
v_a_1765_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1762_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1762_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_realizeGlobalConstNoOverload(v_id_1773_, v_a_1774_, v_a_1775_);
return v_res_1777_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(3863082579u);
v___x_1810_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1811_ = l_Lean_Name_num___override(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1814_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1815_ = l_Lean_Name_str___override(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1818_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1819_ = l_Lean_Name_str___override(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(2u);
v___x_1821_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1822_ = l_Lean_Name_num___override(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1824_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1825_ = 0;
v___x_1826_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1827_ = l_Lean_registerTraceClass(v___x_1824_, v___x_1825_, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1829_;
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

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
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "executeReservedNameAction for "};
static const lean_object* l_Lean_executeReservedNameAction___lam__0___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_executeReservedNameAction___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l_Lean_executeReservedNameAction___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__0_value;
static const lean_ctor_object l_Lean_executeReservedNameAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_executeReservedNameAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l_Lean_executeReservedNameAction___closed__1 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__1_value;
static const lean_string_object l_Lean_executeReservedNameAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_executeReservedNameAction___closed__2 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__2_value;
static const lean_string_object l_Lean_executeReservedNameAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_executeReservedNameAction___closed__3 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__3_value;
static const lean_ctor_object l_Lean_executeReservedNameAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_executeReservedNameAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_executeReservedNameAction___closed__4 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__4_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_executeReservedNameAction___closed__5;
static lean_once_cell_t l_Lean_executeReservedNameAction___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_executeReservedNameAction___closed__6;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(32u);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((size_t)5ULL);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0);
v___x_51_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_47_);
lean_ctor_set(v___x_51_, 3, v___x_47_);
lean_ctor_set_usize(v___x_51_, 4, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; lean_object* v_traceState_55_; lean_object* v_traces_56_; lean_object* v___x_57_; lean_object* v_traceState_58_; lean_object* v_env_59_; lean_object* v_nextMacroScope_60_; lean_object* v_ngen_61_; lean_object* v_auxDeclNGen_62_; lean_object* v_cache_63_; lean_object* v_messages_64_; lean_object* v_infoState_65_; lean_object* v_snapshotTasks_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_85_; 
v___x_54_ = lean_st_ref_get(v___y_52_);
v_traceState_55_ = lean_ctor_get(v___x_54_, 4);
lean_inc_ref(v_traceState_55_);
lean_dec(v___x_54_);
v_traces_56_ = lean_ctor_get(v_traceState_55_, 0);
lean_inc_ref(v_traces_56_);
lean_dec_ref(v_traceState_55_);
v___x_57_ = lean_st_ref_take(v___y_52_);
v_traceState_58_ = lean_ctor_get(v___x_57_, 4);
v_env_59_ = lean_ctor_get(v___x_57_, 0);
v_nextMacroScope_60_ = lean_ctor_get(v___x_57_, 1);
v_ngen_61_ = lean_ctor_get(v___x_57_, 2);
v_auxDeclNGen_62_ = lean_ctor_get(v___x_57_, 3);
v_cache_63_ = lean_ctor_get(v___x_57_, 5);
v_messages_64_ = lean_ctor_get(v___x_57_, 6);
v_infoState_65_ = lean_ctor_get(v___x_57_, 7);
v_snapshotTasks_66_ = lean_ctor_get(v___x_57_, 8);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_85_ == 0)
{
v___x_68_ = v___x_57_;
v_isShared_69_ = v_isSharedCheck_85_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_snapshotTasks_66_);
lean_inc(v_infoState_65_);
lean_inc(v_messages_64_);
lean_inc(v_cache_63_);
lean_inc(v_traceState_58_);
lean_inc(v_auxDeclNGen_62_);
lean_inc(v_ngen_61_);
lean_inc(v_nextMacroScope_60_);
lean_inc(v_env_59_);
lean_dec(v___x_57_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_85_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint64_t v_tid_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_83_; 
v_tid_70_ = lean_ctor_get_uint64(v_traceState_58_, sizeof(void*)*1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_traceState_58_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_traceState_58_, 0);
lean_dec(v_unused_84_);
v___x_72_ = v_traceState_58_;
v_isShared_73_ = v_isSharedCheck_83_;
goto v_resetjp_71_;
}
else
{
lean_dec(v_traceState_58_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_83_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_74_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_74_);
lean_ctor_set_uint64(v_reuseFailAlloc_82_, sizeof(void*)*1, v_tid_70_);
v___x_76_ = v_reuseFailAlloc_82_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_78_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 4, v___x_76_);
v___x_78_ = v___x_68_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_env_59_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_nextMacroScope_60_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_ngen_61_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_auxDeclNGen_62_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v_cache_63_);
lean_ctor_set(v_reuseFailAlloc_81_, 6, v_messages_64_);
lean_ctor_set(v_reuseFailAlloc_81_, 7, v_infoState_65_);
lean_ctor_set(v_reuseFailAlloc_81_, 8, v_snapshotTasks_66_);
v___x_78_ = v_reuseFailAlloc_81_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_st_ref_set(v___y_52_, v___x_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_traces_56_);
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_86_);
lean_dec(v___y_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(lean_object* v_opts_97_, lean_object* v_opt_98_){
_start:
{
lean_object* v_name_99_; lean_object* v_defValue_100_; lean_object* v_map_101_; lean_object* v___x_102_; 
v_name_99_ = lean_ctor_get(v_opt_98_, 0);
v_defValue_100_ = lean_ctor_get(v_opt_98_, 1);
v_map_101_ = lean_ctor_get(v_opts_97_, 0);
v___x_102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_101_, v_name_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
uint8_t v___x_103_; 
v___x_103_ = lean_unbox(v_defValue_100_);
return v___x_103_;
}
else
{
lean_object* v_val_104_; 
v_val_104_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_104_);
lean_dec_ref(v___x_102_);
if (lean_obj_tag(v_val_104_) == 1)
{
uint8_t v_v_105_; 
v_v_105_ = lean_ctor_get_uint8(v_val_104_, 0);
lean_dec_ref(v_val_104_);
return v_v_105_;
}
else
{
uint8_t v___x_106_; 
lean_dec(v_val_104_);
v___x_106_ = lean_unbox(v_defValue_100_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v_opts_107_, lean_object* v_opt_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_107_, v_opt_108_);
lean_dec_ref(v_opt_108_);
lean_dec_ref(v_opts_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_executeReservedNameAction___lam__0___closed__0));
v___x_113_ = l_Lean_stringToMessageData(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object* v_name_114_, lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_obj_once(&l_Lean_executeReservedNameAction___lam__0___closed__1, &l_Lean_executeReservedNameAction___lam__0___closed__1_once, _init_l_Lean_executeReservedNameAction___lam__0___closed__1);
v___x_120_ = l_Lean_MessageData_ofName(v_name_114_);
v___x_121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object* v_name_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_executeReservedNameAction___lam__0(v_name_123_, v_x_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec_ref(v_x_124_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(lean_object* v_opts_129_, lean_object* v_opt_130_){
_start:
{
lean_object* v_name_131_; lean_object* v_defValue_132_; lean_object* v_map_133_; lean_object* v___x_134_; 
v_name_131_ = lean_ctor_get(v_opt_130_, 0);
v_defValue_132_ = lean_ctor_get(v_opt_130_, 1);
v_map_133_ = lean_ctor_get(v_opts_129_, 0);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_133_, v_name_131_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_inc(v_defValue_132_);
return v_defValue_132_;
}
else
{
lean_object* v_val_135_; 
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_134_);
if (lean_obj_tag(v_val_135_) == 3)
{
lean_object* v_v_136_; 
v_v_136_ = lean_ctor_get(v_val_135_, 0);
lean_inc(v_v_136_);
lean_dec_ref(v_val_135_);
return v_v_136_;
}
else
{
lean_dec(v_val_135_);
lean_inc(v_defValue_132_);
return v_defValue_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_137_, v_opt_138_);
lean_dec_ref(v_opt_138_);
lean_dec_ref(v_opts_137_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_e_140_){
_start:
{
if (lean_obj_tag(v_e_140_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 2;
return v___x_141_;
}
else
{
lean_object* v_a_142_; uint8_t v___x_143_; 
v_a_142_ = lean_ctor_get(v_e_140_, 0);
v___x_143_ = lean_unbox(v_a_142_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_e_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_e_146_);
lean_dec_ref(v_e_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
lean_ctor_set(v___x_154_, 2, v___x_153_);
lean_ctor_set(v___x_154_, 3, v___x_153_);
lean_ctor_set(v___x_154_, 4, v___x_152_);
lean_ctor_set(v___x_154_, 5, v___x_152_);
lean_ctor_set(v___x_154_, 6, v___x_152_);
lean_ctor_set(v___x_154_, 7, v___x_152_);
lean_ctor_set(v___x_154_, 8, v___x_152_);
lean_ctor_set(v___x_154_, 9, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(32u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4(void){
_start:
{
size_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((size_t)5ULL);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3);
v___x_163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_159_);
lean_ctor_set(v___x_163_, 3, v___x_159_);
lean_ctor_set_usize(v___x_163_, 4, v___x_158_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_box(1);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; lean_object* v_env_173_; lean_object* v_options_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_172_ = lean_st_ref_get(v___y_170_);
v_env_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc_ref(v_env_173_);
lean_dec(v___x_172_);
v_options_174_ = lean_ctor_get(v___y_169_, 2);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2);
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5);
lean_inc_ref(v_options_174_);
v___x_177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_177_, 0, v_env_173_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
lean_ctor_set(v___x_177_, 3, v_options_174_);
v___x_178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_msgData_168_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___boxed(lean_object* v_msgData_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msgData_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(size_t v_sz_185_, size_t v_i_186_, lean_object* v_bs_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_lt(v_i_186_, v_sz_185_);
if (v___x_188_ == 0)
{
return v_bs_187_;
}
else
{
lean_object* v_v_189_; lean_object* v_msg_190_; lean_object* v___x_191_; lean_object* v_bs_x27_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; 
v_v_189_ = lean_array_uget_borrowed(v_bs_187_, v_i_186_);
v_msg_190_ = lean_ctor_get(v_v_189_, 1);
lean_inc_ref(v_msg_190_);
v___x_191_ = lean_unsigned_to_nat(0u);
v_bs_x27_192_ = lean_array_uset(v_bs_187_, v_i_186_, v___x_191_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_186_, v___x_193_);
v___x_195_ = lean_array_uset(v_bs_x27_192_, v_i_186_, v_msg_190_);
v_i_186_ = v___x_194_;
v_bs_187_ = v___x_195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_197_, lean_object* v_i_198_, lean_object* v_bs_199_){
_start:
{
size_t v_sz_boxed_200_; size_t v_i_boxed_201_; lean_object* v_res_202_; 
v_sz_boxed_200_ = lean_unbox_usize(v_sz_197_);
lean_dec(v_sz_197_);
v_i_boxed_201_ = lean_unbox_usize(v_i_198_);
lean_dec(v_i_198_);
v_res_202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(v_sz_boxed_200_, v_i_boxed_201_, v_bs_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_oldTraces_203_, lean_object* v_data_204_, lean_object* v_ref_205_, lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_fileName_210_; lean_object* v_fileMap_211_; lean_object* v_options_212_; lean_object* v_currRecDepth_213_; lean_object* v_maxRecDepth_214_; lean_object* v_ref_215_; lean_object* v_currNamespace_216_; lean_object* v_openDecls_217_; lean_object* v_initHeartbeats_218_; lean_object* v_maxHeartbeats_219_; lean_object* v_quotContext_220_; lean_object* v_currMacroScope_221_; uint8_t v_diag_222_; lean_object* v_cancelTk_x3f_223_; uint8_t v_suppressElabErrors_224_; lean_object* v_inheritedTraceOptions_225_; lean_object* v___x_226_; lean_object* v_traceState_227_; lean_object* v_traces_228_; lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v___x_231_; size_t v_sz_232_; size_t v___x_233_; lean_object* v___x_234_; lean_object* v_msg_235_; lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_274_; 
v_fileName_210_ = lean_ctor_get(v___y_207_, 0);
v_fileMap_211_ = lean_ctor_get(v___y_207_, 1);
v_options_212_ = lean_ctor_get(v___y_207_, 2);
v_currRecDepth_213_ = lean_ctor_get(v___y_207_, 3);
v_maxRecDepth_214_ = lean_ctor_get(v___y_207_, 4);
v_ref_215_ = lean_ctor_get(v___y_207_, 5);
v_currNamespace_216_ = lean_ctor_get(v___y_207_, 6);
v_openDecls_217_ = lean_ctor_get(v___y_207_, 7);
v_initHeartbeats_218_ = lean_ctor_get(v___y_207_, 8);
v_maxHeartbeats_219_ = lean_ctor_get(v___y_207_, 9);
v_quotContext_220_ = lean_ctor_get(v___y_207_, 10);
v_currMacroScope_221_ = lean_ctor_get(v___y_207_, 11);
v_diag_222_ = lean_ctor_get_uint8(v___y_207_, sizeof(void*)*14);
v_cancelTk_x3f_223_ = lean_ctor_get(v___y_207_, 12);
v_suppressElabErrors_224_ = lean_ctor_get_uint8(v___y_207_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_225_ = lean_ctor_get(v___y_207_, 13);
v___x_226_ = lean_st_ref_get(v___y_208_);
v_traceState_227_ = lean_ctor_get(v___x_226_, 4);
lean_inc_ref(v_traceState_227_);
lean_dec(v___x_226_);
v_traces_228_ = lean_ctor_get(v_traceState_227_, 0);
lean_inc_ref(v_traces_228_);
lean_dec_ref(v_traceState_227_);
v_ref_229_ = l_Lean_replaceRef(v_ref_205_, v_ref_215_);
lean_inc_ref(v_inheritedTraceOptions_225_);
lean_inc(v_cancelTk_x3f_223_);
lean_inc(v_currMacroScope_221_);
lean_inc(v_quotContext_220_);
lean_inc(v_maxHeartbeats_219_);
lean_inc(v_initHeartbeats_218_);
lean_inc(v_openDecls_217_);
lean_inc(v_currNamespace_216_);
lean_inc(v_maxRecDepth_214_);
lean_inc(v_currRecDepth_213_);
lean_inc_ref(v_options_212_);
lean_inc_ref(v_fileMap_211_);
lean_inc_ref(v_fileName_210_);
v___x_230_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_230_, 0, v_fileName_210_);
lean_ctor_set(v___x_230_, 1, v_fileMap_211_);
lean_ctor_set(v___x_230_, 2, v_options_212_);
lean_ctor_set(v___x_230_, 3, v_currRecDepth_213_);
lean_ctor_set(v___x_230_, 4, v_maxRecDepth_214_);
lean_ctor_set(v___x_230_, 5, v_ref_229_);
lean_ctor_set(v___x_230_, 6, v_currNamespace_216_);
lean_ctor_set(v___x_230_, 7, v_openDecls_217_);
lean_ctor_set(v___x_230_, 8, v_initHeartbeats_218_);
lean_ctor_set(v___x_230_, 9, v_maxHeartbeats_219_);
lean_ctor_set(v___x_230_, 10, v_quotContext_220_);
lean_ctor_set(v___x_230_, 11, v_currMacroScope_221_);
lean_ctor_set(v___x_230_, 12, v_cancelTk_x3f_223_);
lean_ctor_set(v___x_230_, 13, v_inheritedTraceOptions_225_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*14, v_diag_222_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*14 + 1, v_suppressElabErrors_224_);
v___x_231_ = l_Lean_PersistentArray_toArray___redArg(v_traces_228_);
lean_dec_ref(v_traces_228_);
v_sz_232_ = lean_array_size(v___x_231_);
v___x_233_ = ((size_t)0ULL);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(v_sz_232_, v___x_233_, v___x_231_);
v_msg_235_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_235_, 0, v_data_204_);
lean_ctor_set(v_msg_235_, 1, v_msg_206_);
lean_ctor_set(v_msg_235_, 2, v___x_234_);
v___x_236_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msg_235_, v___x_230_, v___y_208_);
lean_dec_ref(v___x_230_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_274_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_274_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_274_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v_traceState_242_; lean_object* v_env_243_; lean_object* v_nextMacroScope_244_; lean_object* v_ngen_245_; lean_object* v_auxDeclNGen_246_; lean_object* v_cache_247_; lean_object* v_messages_248_; lean_object* v_infoState_249_; lean_object* v_snapshotTasks_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
v___x_241_ = lean_st_ref_take(v___y_208_);
v_traceState_242_ = lean_ctor_get(v___x_241_, 4);
v_env_243_ = lean_ctor_get(v___x_241_, 0);
v_nextMacroScope_244_ = lean_ctor_get(v___x_241_, 1);
v_ngen_245_ = lean_ctor_get(v___x_241_, 2);
v_auxDeclNGen_246_ = lean_ctor_get(v___x_241_, 3);
v_cache_247_ = lean_ctor_get(v___x_241_, 5);
v_messages_248_ = lean_ctor_get(v___x_241_, 6);
v_infoState_249_ = lean_ctor_get(v___x_241_, 7);
v_snapshotTasks_250_ = lean_ctor_get(v___x_241_, 8);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_273_ == 0)
{
v___x_252_ = v___x_241_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_snapshotTasks_250_);
lean_inc(v_infoState_249_);
lean_inc(v_messages_248_);
lean_inc(v_cache_247_);
lean_inc(v_traceState_242_);
lean_inc(v_auxDeclNGen_246_);
lean_inc(v_ngen_245_);
lean_inc(v_nextMacroScope_244_);
lean_inc(v_env_243_);
lean_dec(v___x_241_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint64_t v_tid_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_271_; 
v_tid_254_ = lean_ctor_get_uint64(v_traceState_242_, sizeof(void*)*1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_traceState_242_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_traceState_242_, 0);
lean_dec(v_unused_272_);
v___x_256_ = v_traceState_242_;
v_isShared_257_ = v_isSharedCheck_271_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_traceState_242_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_271_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_ref_205_);
lean_ctor_set(v___x_258_, 1, v_a_237_);
v___x_259_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_203_, v___x_258_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_259_);
v___x_261_ = v___x_256_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_259_);
lean_ctor_set_uint64(v_reuseFailAlloc_270_, sizeof(void*)*1, v_tid_254_);
v___x_261_ = v_reuseFailAlloc_270_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v___x_261_);
v___x_263_ = v___x_252_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_env_243_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_nextMacroScope_244_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_ngen_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_auxDeclNGen_246_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_cache_247_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_messages_248_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_infoState_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_snapshotTasks_250_);
v___x_263_ = v_reuseFailAlloc_269_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = lean_st_ref_set(v___y_208_, v___x_263_);
v___x_265_ = lean_box(0);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_265_);
v___x_267_ = v___x_239_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_oldTraces_275_, lean_object* v_data_276_, lean_object* v_ref_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_oldTraces_275_, v_data_276_, v_ref_277_, v_msg_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 1);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v_x_283_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v_x_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 0);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg___boxed(lean_object* v_x_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_x_301_);
return v_res_303_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_307_; double v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_float_of_nat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5(void){
_start:
{
lean_object* v___x_312_; double v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1000u);
v___x_313_ = lean_float_of_nat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_314_, uint8_t v_collapsed_315_, lean_object* v_tag_316_, lean_object* v_opts_317_, uint8_t v_clsEnabled_318_, lean_object* v_oldTraces_319_, lean_object* v_msg_320_, lean_object* v_resStartStop_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_424_; 
v_fst_325_ = lean_ctor_get(v_resStartStop_321_, 0);
v_snd_326_ = lean_ctor_get(v_resStartStop_321_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_resStartStop_321_);
if (v_isSharedCheck_424_ == 0)
{
v___x_328_ = v_resStartStop_321_;
v_isShared_329_ = v_isSharedCheck_424_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v_resStartStop_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_424_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v_data_333_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_423_; 
v_fst_344_ = lean_ctor_get(v_snd_326_, 0);
v_snd_345_ = lean_ctor_get(v_snd_326_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_423_ == 0)
{
v___x_347_ = v_snd_326_;
v_isShared_348_ = v_isSharedCheck_423_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_344_);
lean_dec(v_snd_326_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_423_;
goto v_resetjp_346_;
}
v___jp_330_:
{
lean_object* v___x_334_; 
lean_inc(v___y_331_);
v___x_334_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_oldTraces_319_, v_data_333_, v___y_331_, v___y_332_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v___x_334_);
v___x_335_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_fst_325_);
return v___x_335_;
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_fst_325_);
v_a_336_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_334_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
v_resetjp_346_:
{
lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___y_352_; lean_object* v_a_353_; uint8_t v___y_377_; double v___y_408_; 
v___x_349_ = l_Lean_trace_profiler;
v___x_350_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_317_, v___x_349_);
if (v___x_350_ == 0)
{
v___y_377_ = v___x_350_;
goto v___jp_376_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = l_Lean_trace_profiler_useHeartbeats;
v___x_414_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_317_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; double v___x_417_; double v___x_418_; double v___x_419_; 
v___x_415_ = l_Lean_trace_profiler_threshold;
v___x_416_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_317_, v___x_415_);
v___x_417_ = lean_float_of_nat(v___x_416_);
v___x_418_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5);
v___x_419_ = lean_float_div(v___x_417_, v___x_418_);
v___y_408_ = v___x_419_;
goto v___jp_407_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; double v___x_422_; 
v___x_420_ = l_Lean_trace_profiler_threshold;
v___x_421_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_317_, v___x_420_);
v___x_422_ = lean_float_of_nat(v___x_421_);
v___y_408_ = v___x_422_;
goto v___jp_407_;
}
}
v___jp_351_:
{
uint8_t v_result_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v_result_354_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_fst_325_);
v___x_355_ = l_Lean_TraceResult_toEmoji(v_result_354_);
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
v___x_357_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 7);
lean_ctor_set(v___x_347_, 1, v___x_357_);
lean_ctor_set(v___x_347_, 0, v___x_356_);
v___x_359_ = v___x_347_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_370_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v_m_361_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 7);
lean_ctor_set(v___x_328_, 1, v_a_353_);
lean_ctor_set(v___x_328_, 0, v___x_359_);
v_m_361_ = v___x_328_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_353_);
v_m_361_ = v_reuseFailAlloc_369_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; double v___x_364_; lean_object* v_data_365_; 
v___x_362_ = lean_box(v_result_354_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
lean_inc_ref(v_tag_316_);
lean_inc_ref(v___x_363_);
lean_inc(v_cls_314_);
v_data_365_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_365_, 0, v_cls_314_);
lean_ctor_set(v_data_365_, 1, v___x_363_);
lean_ctor_set(v_data_365_, 2, v_tag_316_);
lean_ctor_set_float(v_data_365_, sizeof(void*)*3, v___x_364_);
lean_ctor_set_float(v_data_365_, sizeof(void*)*3 + 8, v___x_364_);
lean_ctor_set_uint8(v_data_365_, sizeof(void*)*3 + 16, v_collapsed_315_);
if (v___x_350_ == 0)
{
lean_dec_ref(v___x_363_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec_ref(v_tag_316_);
lean_dec(v_cls_314_);
v___y_331_ = v___y_352_;
v___y_332_ = v_m_361_;
v_data_333_ = v_data_365_;
goto v___jp_330_;
}
else
{
lean_object* v_data_366_; double v___x_367_; double v___x_368_; 
lean_dec_ref(v_data_365_);
v_data_366_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_366_, 0, v_cls_314_);
lean_ctor_set(v_data_366_, 1, v___x_363_);
lean_ctor_set(v_data_366_, 2, v_tag_316_);
v___x_367_ = lean_unbox_float(v_fst_344_);
lean_dec(v_fst_344_);
lean_ctor_set_float(v_data_366_, sizeof(void*)*3, v___x_367_);
v___x_368_ = lean_unbox_float(v_snd_345_);
lean_dec(v_snd_345_);
lean_ctor_set_float(v_data_366_, sizeof(void*)*3 + 8, v___x_368_);
lean_ctor_set_uint8(v_data_366_, sizeof(void*)*3 + 16, v_collapsed_315_);
v___y_331_ = v___y_352_;
v___y_332_ = v_m_361_;
v_data_333_ = v_data_366_;
goto v___jp_330_;
}
}
}
}
v___jp_371_:
{
lean_object* v_ref_372_; lean_object* v___x_373_; 
v_ref_372_ = lean_ctor_get(v___y_322_, 5);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v_fst_325_);
v___x_373_ = lean_apply_4(v_msg_320_, v_fst_325_, v___y_322_, v___y_323_, lean_box(0));
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
v___y_352_ = v_ref_372_;
v_a_353_ = v_a_374_;
goto v___jp_351_;
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v___x_373_);
v___x_375_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4);
v___y_352_ = v_ref_372_;
v_a_353_ = v___x_375_;
goto v___jp_351_;
}
}
v___jp_376_:
{
if (v_clsEnabled_318_ == 0)
{
if (v___y_377_ == 0)
{
lean_object* v___x_378_; lean_object* v_traceState_379_; lean_object* v_env_380_; lean_object* v_nextMacroScope_381_; lean_object* v_ngen_382_; lean_object* v_auxDeclNGen_383_; lean_object* v_cache_384_; lean_object* v_messages_385_; lean_object* v_infoState_386_; lean_object* v_snapshotTasks_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_del_object(v___x_328_);
lean_dec_ref(v_msg_320_);
lean_dec_ref(v_tag_316_);
lean_dec(v_cls_314_);
v___x_378_ = lean_st_ref_take(v___y_323_);
v_traceState_379_ = lean_ctor_get(v___x_378_, 4);
v_env_380_ = lean_ctor_get(v___x_378_, 0);
v_nextMacroScope_381_ = lean_ctor_get(v___x_378_, 1);
v_ngen_382_ = lean_ctor_get(v___x_378_, 2);
v_auxDeclNGen_383_ = lean_ctor_get(v___x_378_, 3);
v_cache_384_ = lean_ctor_get(v___x_378_, 5);
v_messages_385_ = lean_ctor_get(v___x_378_, 6);
v_infoState_386_ = lean_ctor_get(v___x_378_, 7);
v_snapshotTasks_387_ = lean_ctor_get(v___x_378_, 8);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_406_ == 0)
{
v___x_389_ = v___x_378_;
v_isShared_390_ = v_isSharedCheck_406_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snapshotTasks_387_);
lean_inc(v_infoState_386_);
lean_inc(v_messages_385_);
lean_inc(v_cache_384_);
lean_inc(v_traceState_379_);
lean_inc(v_auxDeclNGen_383_);
lean_inc(v_ngen_382_);
lean_inc(v_nextMacroScope_381_);
lean_inc(v_env_380_);
lean_dec(v___x_378_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_406_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint64_t v_tid_391_; lean_object* v_traces_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_405_; 
v_tid_391_ = lean_ctor_get_uint64(v_traceState_379_, sizeof(void*)*1);
v_traces_392_ = lean_ctor_get(v_traceState_379_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_traceState_379_);
if (v_isSharedCheck_405_ == 0)
{
v___x_394_ = v_traceState_379_;
v_isShared_395_ = v_isSharedCheck_405_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_traces_392_);
lean_dec(v_traceState_379_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_405_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_319_, v_traces_392_);
lean_dec_ref(v_traces_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_396_);
lean_ctor_set_uint64(v_reuseFailAlloc_404_, sizeof(void*)*1, v_tid_391_);
v___x_398_ = v_reuseFailAlloc_404_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 4, v___x_398_);
v___x_400_ = v___x_389_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_env_380_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextMacroScope_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_ngen_382_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_auxDeclNGen_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_messages_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_infoState_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_snapshotTasks_387_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_st_ref_set(v___y_323_, v___x_400_);
v___x_402_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_fst_325_);
return v___x_402_;
}
}
}
}
}
else
{
goto v___jp_371_;
}
}
else
{
goto v___jp_371_;
}
}
v___jp_407_:
{
double v___x_409_; double v___x_410_; double v___x_411_; uint8_t v___x_412_; 
v___x_409_ = lean_unbox_float(v_snd_345_);
v___x_410_ = lean_unbox_float(v_fst_344_);
v___x_411_ = lean_float_sub(v___x_409_, v___x_410_);
v___x_412_ = lean_float_decLt(v___y_408_, v___x_411_);
v___y_377_ = v___x_412_;
goto v___jp_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_425_, lean_object* v_collapsed_426_, lean_object* v_tag_427_, lean_object* v_opts_428_, lean_object* v_clsEnabled_429_, lean_object* v_oldTraces_430_, lean_object* v_msg_431_, lean_object* v_resStartStop_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v_collapsed_boxed_436_; uint8_t v_clsEnabled_boxed_437_; lean_object* v_res_438_; 
v_collapsed_boxed_436_ = lean_unbox(v_collapsed_426_);
v_clsEnabled_boxed_437_ = lean_unbox(v_clsEnabled_429_);
v_res_438_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_425_, v_collapsed_boxed_436_, v_tag_427_, v_opts_428_, v_clsEnabled_boxed_437_, v_oldTraces_430_, v_msg_431_, v_resStartStop_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_opts_428_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_439_, lean_object* v_as_440_, size_t v_i_441_, size_t v_stop_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_441_, v_stop_442_);
if (v___x_446_ == 0)
{
lean_object* v___x_5305__overap_447_; lean_object* v___x_448_; 
v___x_5305__overap_447_ = lean_array_uget_borrowed(v_as_440_, v_i_441_);
lean_inc(v___x_5305__overap_447_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v_name_439_);
v___x_448_ = lean_apply_4(v___x_5305__overap_447_, v_name_439_, v___y_443_, v___y_444_, lean_box(0));
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_unbox(v_a_449_);
if (v___x_453_ == 0)
{
size_t v___x_454_; size_t v___x_455_; 
lean_del_object(v___x_451_);
lean_dec(v_a_449_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_441_, v___x_454_);
v_i_441_ = v___x_455_;
goto _start;
}
else
{
lean_object* v___x_458_; 
lean_dec(v_name_439_);
if (v_isShared_452_ == 0)
{
v___x_458_ = v___x_451_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_449_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_dec(v_name_439_);
return v___x_448_;
}
}
else
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_name_439_);
v___x_461_ = 0;
v___x_462_ = lean_box(v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_464_, lean_object* v_as_465_, lean_object* v_i_466_, lean_object* v_stop_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
size_t v_i_boxed_471_; size_t v_stop_boxed_472_; lean_object* v_res_473_; 
v_i_boxed_471_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_stop_boxed_472_ = lean_unbox_usize(v_stop_467_);
lean_dec(v_stop_467_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_464_, v_as_465_, v_i_boxed_471_, v_stop_boxed_472_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_as_465_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_482_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_483_ = l_Lean_Name_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_484_; double v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1000000000u);
v___x_485_ = lean_float_of_nat(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_options_490_; lean_object* v_inheritedTraceOptions_491_; uint8_t v_hasTrace_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___y_496_; 
v_options_490_ = lean_ctor_get(v_a_487_, 2);
v_inheritedTraceOptions_491_ = lean_ctor_get(v_a_487_, 13);
v_hasTrace_492_ = lean_ctor_get_uint8(v_options_490_, sizeof(void*)*1);
v___x_493_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_494_ = lean_box(0);
if (v_hasTrace_492_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_st_ref_get(v___x_493_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v___x_513_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v___x_513_);
lean_dec(v_name_486_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_494_);
return v___x_517_;
}
else
{
if (v___x_516_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v___x_513_);
lean_dec(v_name_486_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_494_);
return v___x_518_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___x_515_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_486_, v___x_513_, v___x_519_, v___x_520_, v_a_487_, v_a_488_);
lean_dec(v___x_513_);
v___y_496_ = v___x_521_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v___f_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v_a_530_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v_a_545_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v_a_551_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v_a_563_; 
lean_inc(v_name_486_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_522_, 0, v_name_486_);
v___x_523_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_524_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_525_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_491_, v_options_490_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_trace_profiler;
v___x_608_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_490_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
lean_dec_ref(v___f_522_);
v___x_609_ = lean_st_ref_get(v___x_493_);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_array_get_size(v___x_609_);
v___x_612_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec(v___x_609_);
lean_dec(v_name_486_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_494_);
return v___x_613_;
}
else
{
if (v___x_612_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v___x_609_);
lean_dec(v_name_486_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_494_);
return v___x_614_;
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_611_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_486_, v___x_609_, v___x_615_, v___x_616_, v_a_487_, v_a_488_);
lean_dec(v___x_609_);
v___y_496_ = v___x_617_;
goto v___jp_495_;
}
}
}
else
{
goto v___jp_566_;
}
}
else
{
goto v___jp_566_;
}
v___jp_527_:
{
lean_object* v___x_531_; double v___x_532_; double v___x_533_; double v___x_534_; double v___x_535_; double v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_531_ = lean_io_mono_nanos_now();
v___x_532_ = lean_float_of_nat(v___y_529_);
v___x_533_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_534_ = lean_float_div(v___x_532_, v___x_533_);
v___x_535_ = lean_float_of_nat(v___x_531_);
v___x_536_ = lean_float_div(v___x_535_, v___x_533_);
v___x_537_ = lean_box_float(v___x_534_);
v___x_538_ = lean_box_float(v___x_536_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_530_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_523_, v_hasTrace_492_, v___x_524_, v_options_490_, v___x_526_, v___y_528_, v___f_522_, v___x_540_, v_a_487_, v_a_488_);
v___y_496_ = v___x_541_;
goto v___jp_495_;
}
v___jp_542_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(v_a_545_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___y_528_ = v___y_543_;
v___y_529_ = v___y_544_;
v_a_530_ = v___x_547_;
goto v___jp_527_;
}
v___jp_548_:
{
lean_object* v___x_552_; double v___x_553_; double v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_552_ = lean_io_get_num_heartbeats();
v___x_553_ = lean_float_of_nat(v___y_550_);
v___x_554_ = lean_float_of_nat(v___x_552_);
v___x_555_ = lean_box_float(v___x_553_);
v___x_556_ = lean_box_float(v___x_554_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_a_551_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_523_, v_hasTrace_492_, v___x_524_, v_options_490_, v___x_526_, v___y_549_, v___f_522_, v___x_558_, v_a_487_, v_a_488_);
v___y_496_ = v___x_559_;
goto v___jp_495_;
}
v___jp_560_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(v_a_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___y_549_ = v___y_561_;
v___y_550_ = v___y_562_;
v_a_551_ = v___x_565_;
goto v___jp_548_;
}
v___jp_566_:
{
lean_object* v___x_567_; lean_object* v_a_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_567_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_488_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l_Lean_trace_profiler_useHeartbeats;
v___x_570_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_490_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_571_ = lean_io_mono_nanos_now();
v___x_572_ = lean_st_ref_get(v___x_493_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_array_get_size(v___x_572_);
v___x_575_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec(v___x_572_);
lean_dec(v_name_486_);
v___y_543_ = v_a_568_;
v___y_544_ = v___x_571_;
v_a_545_ = v___x_570_;
goto v___jp_542_;
}
else
{
if (v___x_575_ == 0)
{
lean_dec(v___x_572_);
lean_dec(v_name_486_);
v___y_543_ = v_a_568_;
v___y_544_ = v___x_571_;
v_a_545_ = v___x_570_;
goto v___jp_542_;
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_574_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_486_, v___x_572_, v___x_576_, v___x_577_, v_a_487_, v_a_488_);
lean_dec(v___x_572_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; uint8_t v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
v___y_543_ = v_a_568_;
v___y_544_ = v___x_571_;
v_a_545_ = v___x_580_;
goto v___jp_542_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_578_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_578_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_528_ = v_a_568_;
v___y_529_ = v___x_571_;
v_a_530_ = v___x_586_;
goto v___jp_527_;
}
}
}
}
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_589_ = lean_io_get_num_heartbeats();
v___x_590_ = lean_st_ref_get(v___x_493_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v___x_590_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v___x_590_);
lean_dec(v_name_486_);
v___y_561_ = v_a_568_;
v___y_562_ = v___x_589_;
v_a_563_ = v___x_593_;
goto v___jp_560_;
}
else
{
if (v___x_593_ == 0)
{
lean_dec(v___x_590_);
lean_dec(v_name_486_);
v___y_561_ = v_a_568_;
v___y_562_ = v___x_589_;
v_a_563_ = v___x_593_;
goto v___jp_560_;
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_592_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_486_, v___x_590_, v___x_594_, v___x_595_, v_a_487_, v_a_488_);
lean_dec(v___x_590_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref(v___x_596_);
v___x_598_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
v___y_561_ = v_a_568_;
v___y_562_ = v___x_589_;
v_a_563_ = v___x_598_;
goto v___jp_560_;
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_596_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_596_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 0);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
v___y_549_ = v_a_568_;
v___y_550_ = v___x_589_;
v_a_551_ = v___x_604_;
goto v___jp_548_;
}
}
}
}
}
}
}
}
v___jp_495_:
{
if (lean_obj_tag(v___y_496_) == 0)
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_isSharedCheck_503_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___y_496_, 0);
lean_dec(v_unused_504_);
v___x_498_ = v___y_496_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___y_496_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_494_);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_494_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___y_496_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___y_496_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___y_496_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_executeReservedNameAction(v_name_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_00_u03b1_623_, lean_object* v_x_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_x_624_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_00_u03b1_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_00_u03b1_629_, v_x_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_642_, uint8_t v_suppressElabErrors_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 1)
{
lean_object* v_pre_645_; 
v_pre_645_ = lean_ctor_get(v_x_644_, 0);
switch(lean_obj_tag(v_pre_645_))
{
case 1:
{
lean_object* v_pre_646_; 
v_pre_646_ = lean_ctor_get(v_pre_645_, 0);
switch(lean_obj_tag(v_pre_646_))
{
case 0:
{
lean_object* v_str_647_; lean_object* v_str_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_str_647_ = lean_ctor_get(v_x_644_, 1);
v_str_648_ = lean_ctor_get(v_pre_645_, 1);
v___x_649_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_650_ = lean_string_dec_eq(v_str_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_652_ = lean_string_dec_eq(v_str_648_, v___x_651_);
if (v___x_652_ == 0)
{
return v___y_642_;
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_654_ = lean_string_dec_eq(v_str_647_, v___x_653_);
if (v___x_654_ == 0)
{
return v___y_642_;
}
else
{
return v_suppressElabErrors_643_;
}
}
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_656_ = lean_string_dec_eq(v_str_647_, v___x_655_);
if (v___x_656_ == 0)
{
return v___y_642_;
}
else
{
return v_suppressElabErrors_643_;
}
}
}
case 1:
{
lean_object* v_pre_657_; 
v_pre_657_ = lean_ctor_get(v_pre_646_, 0);
if (lean_obj_tag(v_pre_657_) == 0)
{
lean_object* v_str_658_; lean_object* v_str_659_; lean_object* v_str_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_str_658_ = lean_ctor_get(v_x_644_, 1);
v_str_659_ = lean_ctor_get(v_pre_645_, 1);
v_str_660_ = lean_ctor_get(v_pre_646_, 1);
v___x_661_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_662_ = lean_string_dec_eq(v_str_660_, v___x_661_);
if (v___x_662_ == 0)
{
return v___y_642_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_664_ = lean_string_dec_eq(v_str_659_, v___x_663_);
if (v___x_664_ == 0)
{
return v___y_642_;
}
else
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_666_ = lean_string_dec_eq(v_str_658_, v___x_665_);
if (v___x_666_ == 0)
{
return v___y_642_;
}
else
{
return v_suppressElabErrors_643_;
}
}
}
}
else
{
return v___y_642_;
}
}
default: 
{
return v___y_642_;
}
}
}
case 0:
{
lean_object* v_str_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_str_667_ = lean_ctor_get(v_x_644_, 1);
v___x_668_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_669_ = lean_string_dec_eq(v_str_667_, v___x_668_);
if (v___x_669_ == 0)
{
return v___y_642_;
}
else
{
return v_suppressElabErrors_643_;
}
}
default: 
{
return v___y_642_;
}
}
}
else
{
return v___y_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_670_, lean_object* v_suppressElabErrors_671_, lean_object* v_x_672_){
_start:
{
uint8_t v___y_4690__boxed_673_; uint8_t v_suppressElabErrors_boxed_674_; uint8_t v_res_675_; lean_object* v_r_676_; 
v___y_4690__boxed_673_ = lean_unbox(v___y_670_);
v_suppressElabErrors_boxed_674_ = lean_unbox(v_suppressElabErrors_671_);
v_res_675_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4690__boxed_673_, v_suppressElabErrors_boxed_674_, v_x_672_);
lean_dec(v_x_672_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_677_, lean_object* v_msgData_678_, uint8_t v_severity_679_, uint8_t v_isSilent_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; lean_object* v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; lean_object* v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; uint8_t v___y_763_; uint8_t v___x_768_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; uint8_t v___y_773_; lean_object* v___y_774_; uint8_t v___y_775_; uint8_t v___y_776_; uint8_t v___y_778_; uint8_t v___x_793_; 
v___x_768_ = 2;
v___x_793_ = l_Lean_instBEqMessageSeverity_beq(v_severity_679_, v___x_768_);
if (v___x_793_ == 0)
{
v___y_778_ = v___x_793_;
goto v___jp_777_;
}
else
{
uint8_t v___x_794_; 
lean_inc_ref(v_msgData_678_);
v___x_794_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_678_);
v___y_778_ = v___x_794_;
goto v___jp_777_;
}
v___jp_684_:
{
lean_object* v___x_694_; lean_object* v_currNamespace_695_; lean_object* v_openDecls_696_; lean_object* v_env_697_; lean_object* v_nextMacroScope_698_; lean_object* v_ngen_699_; lean_object* v_auxDeclNGen_700_; lean_object* v_traceState_701_; lean_object* v_cache_702_; lean_object* v_messages_703_; lean_object* v_infoState_704_; lean_object* v_snapshotTasks_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_719_; 
v___x_694_ = lean_st_ref_take(v___y_693_);
v_currNamespace_695_ = lean_ctor_get(v___y_692_, 6);
v_openDecls_696_ = lean_ctor_get(v___y_692_, 7);
v_env_697_ = lean_ctor_get(v___x_694_, 0);
v_nextMacroScope_698_ = lean_ctor_get(v___x_694_, 1);
v_ngen_699_ = lean_ctor_get(v___x_694_, 2);
v_auxDeclNGen_700_ = lean_ctor_get(v___x_694_, 3);
v_traceState_701_ = lean_ctor_get(v___x_694_, 4);
v_cache_702_ = lean_ctor_get(v___x_694_, 5);
v_messages_703_ = lean_ctor_get(v___x_694_, 6);
v_infoState_704_ = lean_ctor_get(v___x_694_, 7);
v_snapshotTasks_705_ = lean_ctor_get(v___x_694_, 8);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_719_ == 0)
{
v___x_707_ = v___x_694_;
v_isShared_708_ = v_isSharedCheck_719_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snapshotTasks_705_);
lean_inc(v_infoState_704_);
lean_inc(v_messages_703_);
lean_inc(v_cache_702_);
lean_inc(v_traceState_701_);
lean_inc(v_auxDeclNGen_700_);
lean_inc(v_ngen_699_);
lean_inc(v_nextMacroScope_698_);
lean_inc(v_env_697_);
lean_dec(v___x_694_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_719_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
lean_inc(v_openDecls_696_);
lean_inc(v_currNamespace_695_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_currNamespace_695_);
lean_ctor_set(v___x_709_, 1, v_openDecls_696_);
v___x_710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___y_689_);
lean_inc_ref(v___y_686_);
lean_inc_ref(v___y_690_);
v___x_711_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_711_, 0, v___y_690_);
lean_ctor_set(v___x_711_, 1, v___y_688_);
lean_ctor_set(v___x_711_, 2, v___y_687_);
lean_ctor_set(v___x_711_, 3, v___y_686_);
lean_ctor_set(v___x_711_, 4, v___x_710_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5, v___y_685_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5 + 1, v___y_691_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5 + 2, v_isSilent_680_);
v___x_712_ = l_Lean_MessageLog_add(v___x_711_, v_messages_703_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 6, v___x_712_);
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_env_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_nextMacroScope_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_ngen_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_auxDeclNGen_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_traceState_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_cache_702_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_infoState_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_snapshotTasks_705_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_st_ref_set(v___y_693_, v___x_714_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
v___jp_720_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_744_; 
v___x_729_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_678_);
v___x_730_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v___x_729_, v___y_681_, v___y_682_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_744_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_744_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_744_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_inc_ref_n(v___y_723_, 2);
v___x_735_ = l_Lean_FileMap_toPosition(v___y_723_, v___y_724_);
lean_dec(v___y_724_);
v___x_736_ = l_Lean_FileMap_toPosition(v___y_723_, v___y_728_);
lean_dec(v___y_728_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_725_ == 0)
{
lean_del_object(v___x_733_);
lean_dec_ref(v___y_721_);
v___y_685_ = v___y_722_;
v___y_686_ = v___x_738_;
v___y_687_ = v___x_737_;
v___y_688_ = v___x_735_;
v___y_689_ = v_a_731_;
v___y_690_ = v___y_726_;
v___y_691_ = v___y_727_;
v___y_692_ = v___y_681_;
v___y_693_ = v___y_682_;
goto v___jp_684_;
}
else
{
uint8_t v___x_739_; 
lean_inc(v_a_731_);
v___x_739_ = l_Lean_MessageData_hasTag(v___y_721_, v_a_731_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec_ref(v___x_737_);
lean_dec_ref(v___x_735_);
lean_dec(v_a_731_);
v___x_740_ = lean_box(0);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_740_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_del_object(v___x_733_);
v___y_685_ = v___y_722_;
v___y_686_ = v___x_738_;
v___y_687_ = v___x_737_;
v___y_688_ = v___x_735_;
v___y_689_ = v_a_731_;
v___y_690_ = v___y_726_;
v___y_691_ = v___y_727_;
v___y_692_ = v___y_681_;
v___y_693_ = v___y_682_;
goto v___jp_684_;
}
}
}
}
v___jp_745_:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Syntax_getTailPos_x3f(v___y_749_, v___y_748_);
lean_dec(v___y_749_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_inc(v___y_753_);
v___y_721_ = v___y_746_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_747_;
v___y_724_ = v___y_753_;
v___y_725_ = v___y_750_;
v___y_726_ = v___y_751_;
v___y_727_ = v___y_752_;
v___y_728_ = v___y_753_;
goto v___jp_720_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v___x_754_);
v___y_721_ = v___y_746_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_747_;
v___y_724_ = v___y_753_;
v___y_725_ = v___y_750_;
v___y_726_ = v___y_751_;
v___y_727_ = v___y_752_;
v___y_728_ = v_val_755_;
goto v___jp_720_;
}
}
v___jp_756_:
{
lean_object* v_ref_764_; lean_object* v___x_765_; 
v_ref_764_ = l_Lean_replaceRef(v_ref_677_, v___y_761_);
v___x_765_ = l_Lean_Syntax_getPos_x3f(v_ref_764_, v___y_758_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_758_;
v___y_749_ = v_ref_764_;
v___y_750_ = v___y_760_;
v___y_751_ = v___y_762_;
v___y_752_ = v___y_763_;
v___y_753_ = v___x_766_;
goto v___jp_745_;
}
else
{
lean_object* v_val_767_; 
v_val_767_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v___x_765_);
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_758_;
v___y_749_ = v_ref_764_;
v___y_750_ = v___y_760_;
v___y_751_ = v___y_762_;
v___y_752_ = v___y_763_;
v___y_753_ = v_val_767_;
goto v___jp_745_;
}
}
v___jp_769_:
{
if (v___y_776_ == 0)
{
v___y_757_ = v___y_771_;
v___y_758_ = v___y_775_;
v___y_759_ = v___y_770_;
v___y_760_ = v___y_773_;
v___y_761_ = v___y_772_;
v___y_762_ = v___y_774_;
v___y_763_ = v_severity_679_;
goto v___jp_756_;
}
else
{
v___y_757_ = v___y_771_;
v___y_758_ = v___y_775_;
v___y_759_ = v___y_770_;
v___y_760_ = v___y_773_;
v___y_761_ = v___y_772_;
v___y_762_ = v___y_774_;
v___y_763_ = v___x_768_;
goto v___jp_756_;
}
}
v___jp_777_:
{
if (v___y_778_ == 0)
{
lean_object* v_fileName_779_; lean_object* v_fileMap_780_; lean_object* v_options_781_; lean_object* v_ref_782_; uint8_t v_suppressElabErrors_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___f_786_; uint8_t v___x_787_; uint8_t v___x_788_; 
v_fileName_779_ = lean_ctor_get(v___y_681_, 0);
v_fileMap_780_ = lean_ctor_get(v___y_681_, 1);
v_options_781_ = lean_ctor_get(v___y_681_, 2);
v_ref_782_ = lean_ctor_get(v___y_681_, 5);
v_suppressElabErrors_783_ = lean_ctor_get_uint8(v___y_681_, sizeof(void*)*14 + 1);
v___x_784_ = lean_box(v___y_778_);
v___x_785_ = lean_box(v_suppressElabErrors_783_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_786_, 0, v___x_784_);
lean_closure_set(v___f_786_, 1, v___x_785_);
v___x_787_ = 1;
v___x_788_ = l_Lean_instBEqMessageSeverity_beq(v_severity_679_, v___x_787_);
if (v___x_788_ == 0)
{
v___y_770_ = v_fileMap_780_;
v___y_771_ = v___f_786_;
v___y_772_ = v_ref_782_;
v___y_773_ = v_suppressElabErrors_783_;
v___y_774_ = v_fileName_779_;
v___y_775_ = v___y_778_;
v___y_776_ = v___x_788_;
goto v___jp_769_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = l_Lean_warningAsError;
v___x_790_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_781_, v___x_789_);
v___y_770_ = v_fileMap_780_;
v___y_771_ = v___f_786_;
v___y_772_ = v_ref_782_;
v___y_773_ = v_suppressElabErrors_783_;
v___y_774_ = v_fileName_779_;
v___y_775_ = v___y_778_;
v___y_776_ = v___x_790_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_msgData_678_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_795_, lean_object* v_msgData_796_, lean_object* v_severity_797_, lean_object* v_isSilent_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v_severity_boxed_802_; uint8_t v_isSilent_boxed_803_; lean_object* v_res_804_; 
v_severity_boxed_802_ = lean_unbox(v_severity_797_);
v_isSilent_boxed_803_ = lean_unbox(v_isSilent_798_);
v_res_804_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_795_, v_msgData_796_, v_severity_boxed_802_, v_isSilent_boxed_803_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v_ref_795_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_805_, uint8_t v_severity_806_, uint8_t v_isSilent_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_ref_811_; lean_object* v___x_812_; 
v_ref_811_ = lean_ctor_get(v___y_808_, 5);
v___x_812_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_811_, v_msgData_805_, v_severity_806_, v_isSilent_807_, v___y_808_, v___y_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_813_, lean_object* v_severity_814_, lean_object* v_isSilent_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
uint8_t v_severity_boxed_819_; uint8_t v_isSilent_boxed_820_; lean_object* v_res_821_; 
v_severity_boxed_819_ = lean_unbox(v_severity_814_);
v_isSilent_boxed_820_ = lean_unbox(v_isSilent_815_);
v_res_821_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_813_, v_severity_boxed_819_, v_isSilent_boxed_820_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
uint8_t v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; 
v___x_826_ = 2;
v___x_827_ = 0;
v___x_828_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_822_, v___x_826_, v___x_827_, v___y_823_, v___y_824_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_833_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_object* v___x_846_; 
lean_dec(v_id_840_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_x_842_);
return v___x_846_;
}
else
{
lean_object* v_head_847_; lean_object* v_tail_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_905_; 
v_head_847_ = lean_ctor_get(v_x_841_, 0);
v_tail_848_ = lean_ctor_get(v_x_841_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_841_);
if (v_isSharedCheck_905_ == 0)
{
v___x_850_ = v_x_841_;
v_isShared_851_ = v_isSharedCheck_905_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_tail_848_);
lean_inc(v_head_847_);
lean_dec(v_x_841_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_905_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_fst_857_; lean_object* v___x_858_; lean_object* v_env_859_; uint8_t v___x_860_; uint8_t v___x_861_; 
v_fst_857_ = lean_ctor_get(v_head_847_, 0);
v___x_858_ = lean_st_ref_get(v___y_844_);
v_env_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_ref(v_env_859_);
lean_dec(v___x_858_);
v___x_860_ = 1;
lean_inc(v_fst_857_);
v___x_861_ = l_Lean_Environment_contains(v_env_859_, v_fst_857_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_inc(v_fst_857_);
v___x_862_ = l_Lean_executeReservedNameAction(v_fst_857_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; lean_object* v_env_864_; uint8_t v___x_865_; 
lean_dec_ref(v___x_862_);
v___x_863_ = lean_st_ref_get(v___y_844_);
v_env_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_env_864_);
lean_dec(v___x_863_);
v___x_865_ = l_Lean_Environment_containsOnBranch(v_env_864_, v_fst_857_);
lean_dec_ref(v_env_864_);
if (v___x_865_ == 0)
{
lean_del_object(v___x_850_);
lean_dec(v_head_847_);
v_x_841_ = v_tail_848_;
goto _start;
}
else
{
goto v___jp_852_;
}
}
else
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_902_; 
lean_del_object(v___x_850_);
v_isSharedCheck_902_ = !lean_is_exclusive(v_head_847_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; 
v_unused_903_ = lean_ctor_get(v_head_847_, 1);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_head_847_, 0);
lean_dec(v_unused_904_);
v___x_868_ = v_head_847_;
v_isShared_869_ = v_isSharedCheck_902_;
goto v_resetjp_867_;
}
else
{
lean_dec(v_head_847_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_902_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_901_; 
v_a_870_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_901_ == 0)
{
v___x_872_ = v___x_862_;
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___y_875_; uint8_t v___x_899_; 
v___x_899_ = l_Lean_Exception_isInterrupt(v_a_870_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; 
lean_inc(v_a_870_);
v___x_900_ = l_Lean_Exception_isRuntime(v_a_870_);
v___y_875_ = v___x_900_;
goto v___jp_874_;
}
else
{
v___y_875_ = v___x_899_;
goto v___jp_874_;
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
lean_del_object(v___x_872_);
v___x_876_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_840_);
v___x_877_ = l_Lean_MessageData_ofName(v_id_840_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 7);
lean_ctor_set(v___x_868_, 1, v___x_877_);
lean_ctor_set(v___x_868_, 0, v___x_876_);
v___x_879_ = v___x_868_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_895_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_Exception_toMessageData(v_a_870_);
v___x_883_ = l_Lean_indentD(v___x_882_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_881_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_884_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_dec_ref(v___x_885_);
v_x_841_ = v_tail_848_;
goto _start;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_tail_848_);
lean_dec(v_x_842_);
lean_dec(v_id_840_);
v_a_887_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_885_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v___x_897_; 
lean_del_object(v___x_868_);
lean_dec(v_tail_848_);
lean_dec(v_x_842_);
lean_dec(v_id_840_);
if (v_isShared_873_ == 0)
{
v___x_897_ = v___x_872_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_870_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
}
else
{
goto v___jp_852_;
}
v___jp_852_:
{
lean_object* v___x_854_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_x_842_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_head_847_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_x_842_);
v___x_854_ = v_reuseFailAlloc_856_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
v_x_841_ = v_tail_848_;
v_x_842_ = v___x_854_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_906_, v_x_907_, v_x_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(lean_object* v_msgData_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v___x_917_ = 1;
v___x_918_ = 0;
v___x_919_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_913_, v___x_917_, v___x_918_, v___y_914_, v___y_915_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v_msgData_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(lean_object* v_opt_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_options_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_options_928_ = lean_ctor_get(v___y_926_, 2);
v___x_929_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_928_, v_opt_925_);
v___x_930_ = lean_box(v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_opt_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_932_, v___y_933_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_opt_932_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__0));
v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__2));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_id_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v_env_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_969_; 
v___x_946_ = lean_st_ref_get(v___y_944_);
v_env_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref(v_env_947_);
lean_dec(v___x_946_);
v___x_948_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_949_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v___x_948_, v___y_943_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_969_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v_isExporting_959_; 
v_isExporting_959_ = lean_ctor_get_uint8(v_env_947_, sizeof(void*)*8);
lean_dec_ref(v_env_947_);
if (v_isExporting_959_ == 0)
{
lean_dec(v_a_950_);
lean_dec(v_id_942_);
goto v___jp_954_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_isPrivateName(v_id_942_);
if (v___x_960_ == 0)
{
lean_dec(v_a_950_);
lean_dec(v_id_942_);
goto v___jp_954_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = lean_unbox(v_a_950_);
lean_dec(v_a_950_);
if (v___x_961_ == 0)
{
lean_dec(v_id_942_);
goto v___jp_954_;
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_952_);
v___x_962_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__1);
v___x_963_ = 0;
v___x_964_ = l_Lean_MessageData_ofConstName(v_id_942_, v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_962_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___closed__3);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__5(v___x_967_, v___y_943_, v___y_944_);
return v___x_968_;
}
}
}
v___jp_954_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_id_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_id_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_974_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(lean_object* v_x_975_){
_start:
{
lean_object* v_fst_976_; uint8_t v___x_977_; 
v_fst_976_ = lean_ctor_get(v_x_975_, 0);
v___x_977_ = l_Lean_isPrivateName(v_fst_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0___boxed(lean_object* v_x_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___lam__0(v_x_978_);
lean_dec_ref(v_x_978_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_982_, uint8_t v_enableLog_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_env_988_; lean_object* v_options_989_; lean_object* v_currNamespace_990_; lean_object* v_openDecls_991_; lean_object* v___x_992_; lean_object* v_env_993_; lean_object* v_res_994_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v_options_989_ = lean_ctor_get(v___y_984_, 2);
v_currNamespace_990_ = lean_ctor_get(v___y_984_, 6);
v_openDecls_991_ = lean_ctor_get(v___y_984_, 7);
v___x_992_ = lean_st_ref_get(v___y_985_);
v_env_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc_ref(v_env_993_);
lean_dec(v___x_992_);
lean_inc(v_openDecls_991_);
lean_inc(v_currNamespace_990_);
v_res_994_ = l_Lean_ResolveName_resolveGlobalName(v_env_988_, v_options_989_, v_currNamespace_990_, v_openDecls_991_, v_id_982_);
if (v_enableLog_983_ == 0)
{
lean_object* v___x_995_; 
lean_dec_ref(v_env_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v_res_994_);
return v___x_995_;
}
else
{
uint8_t v_isExporting_996_; 
v_isExporting_996_ = lean_ctor_get_uint8(v_env_993_, sizeof(void*)*8);
lean_dec_ref(v_env_993_);
if (v_isExporting_996_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_res_994_);
return v___x_997_;
}
else
{
lean_object* v___f_998_; lean_object* v___x_999_; 
v___f_998_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___closed__0));
lean_inc(v_res_994_);
v___x_999_ = l_List_find_x3f___redArg(v___f_998_, v_res_994_);
if (lean_obj_tag(v___x_999_) == 1)
{
lean_object* v_val_1000_; lean_object* v_fst_1001_; lean_object* v___x_1002_; 
v_val_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref(v___x_999_);
v_fst_1001_ = lean_ctor_get(v_val_1000_, 0);
lean_inc(v_fst_1001_);
lean_dec(v_val_1000_);
v___x_1002_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_fst_1001_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1010_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_res_994_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_res_994_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_res_994_);
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v___x_1019_; 
lean_dec(v___x_999_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_res_994_);
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_1020_, lean_object* v_enableLog_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v_enableLog_boxed_1025_; lean_object* v_res_1026_; 
v_enableLog_boxed_1025_ = lean_unbox(v_enableLog_1021_);
v_res_1026_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1020_, v_enableLog_boxed_1025_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 1;
lean_inc(v_id_1027_);
v___x_1032_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1027_, v___x_1031_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1027_, v_a_1033_, v___x_1034_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = l_List_reverse___redArg(v_a_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
return v___x_1035_;
}
}
else
{
lean_dec(v_id_1027_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_realizeGlobalName(v_id_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(lean_object* v_opt_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___redArg(v_opt_1050_, v___y_1051_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4___boxed(lean_object* v_opt_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2_spec__4(v_opt_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_opt_1055_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = l_List_reverse___redArg(v_a_1061_);
return v___x_1062_;
}
else
{
lean_object* v_head_1063_; lean_object* v_tail_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_head_1063_ = lean_ctor_get(v_a_1060_, 0);
v_tail_1064_ = lean_ctor_get(v_a_1060_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_a_1060_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_a_1060_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_tail_1064_);
lean_inc(v_head_1063_);
lean_dec(v_a_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_fst_1068_; lean_object* v___x_1070_; 
v_fst_1068_ = lean_ctor_get(v_head_1063_, 0);
lean_inc(v_fst_1068_);
lean_dec(v_head_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_a_1061_);
lean_ctor_set(v___x_1066_, 0, v_fst_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_a_1061_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
v_a_1060_ = v_tail_1064_;
v_a_1061_ = v___x_1070_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_ref_1078_; lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
v_ref_1078_ = lean_ctor_get(v___y_1075_, 5);
v___x_1079_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msg_1074_, v___y_1075_, v___y_1076_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_inc(v_ref_1078_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_ref_1078_);
lean_ctor_set(v___x_1084_, 1, v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1094_, lean_object* v_msg_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_fileName_1099_; lean_object* v_fileMap_1100_; lean_object* v_options_1101_; lean_object* v_currRecDepth_1102_; lean_object* v_maxRecDepth_1103_; lean_object* v_ref_1104_; lean_object* v_currNamespace_1105_; lean_object* v_openDecls_1106_; lean_object* v_initHeartbeats_1107_; lean_object* v_maxHeartbeats_1108_; lean_object* v_quotContext_1109_; lean_object* v_currMacroScope_1110_; uint8_t v_diag_1111_; lean_object* v_cancelTk_x3f_1112_; uint8_t v_suppressElabErrors_1113_; lean_object* v_inheritedTraceOptions_1114_; lean_object* v_ref_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_fileName_1099_ = lean_ctor_get(v___y_1096_, 0);
v_fileMap_1100_ = lean_ctor_get(v___y_1096_, 1);
v_options_1101_ = lean_ctor_get(v___y_1096_, 2);
v_currRecDepth_1102_ = lean_ctor_get(v___y_1096_, 3);
v_maxRecDepth_1103_ = lean_ctor_get(v___y_1096_, 4);
v_ref_1104_ = lean_ctor_get(v___y_1096_, 5);
v_currNamespace_1105_ = lean_ctor_get(v___y_1096_, 6);
v_openDecls_1106_ = lean_ctor_get(v___y_1096_, 7);
v_initHeartbeats_1107_ = lean_ctor_get(v___y_1096_, 8);
v_maxHeartbeats_1108_ = lean_ctor_get(v___y_1096_, 9);
v_quotContext_1109_ = lean_ctor_get(v___y_1096_, 10);
v_currMacroScope_1110_ = lean_ctor_get(v___y_1096_, 11);
v_diag_1111_ = lean_ctor_get_uint8(v___y_1096_, sizeof(void*)*14);
v_cancelTk_x3f_1112_ = lean_ctor_get(v___y_1096_, 12);
v_suppressElabErrors_1113_ = lean_ctor_get_uint8(v___y_1096_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1114_ = lean_ctor_get(v___y_1096_, 13);
v_ref_1115_ = l_Lean_replaceRef(v_ref_1094_, v_ref_1104_);
lean_inc_ref(v_inheritedTraceOptions_1114_);
lean_inc(v_cancelTk_x3f_1112_);
lean_inc(v_currMacroScope_1110_);
lean_inc(v_quotContext_1109_);
lean_inc(v_maxHeartbeats_1108_);
lean_inc(v_initHeartbeats_1107_);
lean_inc(v_openDecls_1106_);
lean_inc(v_currNamespace_1105_);
lean_inc(v_maxRecDepth_1103_);
lean_inc(v_currRecDepth_1102_);
lean_inc_ref(v_options_1101_);
lean_inc_ref(v_fileMap_1100_);
lean_inc_ref(v_fileName_1099_);
v___x_1116_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1116_, 0, v_fileName_1099_);
lean_ctor_set(v___x_1116_, 1, v_fileMap_1100_);
lean_ctor_set(v___x_1116_, 2, v_options_1101_);
lean_ctor_set(v___x_1116_, 3, v_currRecDepth_1102_);
lean_ctor_set(v___x_1116_, 4, v_maxRecDepth_1103_);
lean_ctor_set(v___x_1116_, 5, v_ref_1115_);
lean_ctor_set(v___x_1116_, 6, v_currNamespace_1105_);
lean_ctor_set(v___x_1116_, 7, v_openDecls_1106_);
lean_ctor_set(v___x_1116_, 8, v_initHeartbeats_1107_);
lean_ctor_set(v___x_1116_, 9, v_maxHeartbeats_1108_);
lean_ctor_set(v___x_1116_, 10, v_quotContext_1109_);
lean_ctor_set(v___x_1116_, 11, v_currMacroScope_1110_);
lean_ctor_set(v___x_1116_, 12, v_cancelTk_x3f_1112_);
lean_ctor_set(v___x_1116_, 13, v_inheritedTraceOptions_1114_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*14, v_diag_1111_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*14 + 1, v_suppressElabErrors_1113_);
v___x_1117_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1095_, v___x_1116_, v___y_1097_);
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1118_, v_msg_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v_ref_1118_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1145_, lean_object* v_declHint_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_env_1150_; uint8_t v___x_1151_; 
v___x_1149_ = lean_st_ref_get(v___y_1147_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_env_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_Name_isAnonymous(v_declHint_1146_);
if (v___x_1151_ == 0)
{
uint8_t v_isExporting_1152_; 
v_isExporting_1152_ = lean_ctor_get_uint8(v_env_1150_, sizeof(void*)*8);
if (v_isExporting_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec_ref(v_env_1150_);
lean_dec(v_declHint_1146_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1145_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
lean_inc_ref(v_env_1150_);
v___x_1154_ = l_Lean_Environment_setExporting(v_env_1150_, v___x_1151_);
lean_inc(v_declHint_1146_);
lean_inc_ref(v___x_1154_);
v___x_1155_ = l_Lean_Environment_contains(v___x_1154_, v_declHint_1146_, v_isExporting_1152_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_env_1150_);
lean_dec(v_declHint_1146_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_msg_1145_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_c_1162_; lean_object* v___x_1163_; 
v___x_1157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2);
v___x_1158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5);
v___x_1159_ = l_Lean_Options_empty;
v___x_1160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1154_);
lean_ctor_set(v___x_1160_, 1, v___x_1157_);
lean_ctor_set(v___x_1160_, 2, v___x_1158_);
lean_ctor_set(v___x_1160_, 3, v___x_1159_);
lean_inc(v_declHint_1146_);
v___x_1161_ = l_Lean_MessageData_ofConstName(v_declHint_1146_, v___x_1151_);
v_c_1162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1162_, 0, v___x_1160_);
lean_ctor_set(v_c_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1150_, v_declHint_1146_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec_ref(v_env_1150_);
lean_dec(v_declHint_1146_);
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_c_1162_);
v___x_1166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_note(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_msg_1145_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1206_; 
v_val_1171_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1173_ = v___x_1163_;
v_isShared_1174_ = v_isSharedCheck_1206_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v___x_1163_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1206_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_mod_1178_; uint8_t v___x_1179_; 
v___x_1175_ = lean_box(0);
v___x_1176_ = l_Lean_Environment_header(v_env_1150_);
lean_dec_ref(v_env_1150_);
v___x_1177_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1176_);
v_mod_1178_ = lean_array_get(v___x_1175_, v___x_1177_, v_val_1171_);
lean_dec(v_val_1171_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = l_Lean_isPrivateName(v_declHint_1146_);
lean_dec(v_declHint_1146_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_c_1162_);
v___x_1182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_MessageData_ofName(v_mod_1178_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_MessageData_note(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_msg_1145_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1189_);
v___x_1191_ = v___x_1173_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_c_1162_);
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_MessageData_ofName(v_mod_1178_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Lean_MessageData_note(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_msg_1145_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1202_);
v___x_1204_ = v___x_1173_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1207_; 
lean_dec_ref(v_env_1150_);
lean_dec(v_declHint_1146_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_msg_1145_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1208_, lean_object* v_declHint_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1208_, v_declHint_1209_, v___y_1210_);
lean_dec(v___y_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1213_, lean_object* v_declHint_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v___x_1218_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1213_, v_declHint_1214_, v___y_1216_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = l_Lean_unknownIdentifierMessageTag;
v___x_1224_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1229_, lean_object* v_declHint_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1229_, v_declHint_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1235_, v_a_1242_, v___y_1238_, v___y_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1244_, lean_object* v_msg_1245_, lean_object* v_declHint_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1244_, v_msg_1245_, v_declHint_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v_ref_1244_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1257_, lean_object* v_constName_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1263_ = 0;
lean_inc(v_constName_1258_);
v___x_1264_ = l_Lean_MessageData_ofConstName(v_constName_1258_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1262_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1257_, v___x_1267_, v_constName_1258_, v___y_1259_, v___y_1260_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1269_, lean_object* v_constName_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1269_, v_constName_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v_ref_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
if (lean_obj_tag(v_a_1275_) == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = l_List_reverse___redArg(v_a_1276_);
return v___x_1277_;
}
else
{
lean_object* v_head_1278_; lean_object* v_tail_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1290_; 
v_head_1278_ = lean_ctor_get(v_a_1275_, 0);
v_tail_1279_ = lean_ctor_get(v_a_1275_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1275_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1281_ = v_a_1275_;
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_tail_1279_);
lean_inc(v_head_1278_);
lean_dec(v_a_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_snd_1283_; uint8_t v___x_1284_; 
v_snd_1283_ = lean_ctor_get(v_head_1278_, 1);
v___x_1284_ = l_List_isEmpty___redArg(v_snd_1283_);
if (v___x_1284_ == 0)
{
lean_del_object(v___x_1281_);
lean_dec(v_head_1278_);
v_a_1275_ = v_tail_1279_;
goto _start;
}
else
{
lean_object* v___x_1287_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v_a_1276_);
v___x_1287_ = v___x_1281_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_head_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_a_1276_);
v___x_1287_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v_a_1275_ = v_tail_1279_;
v_a_1276_ = v___x_1287_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1291_, lean_object* v_cs_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_cs_1297_; uint8_t v___x_1301_; 
v___x_1296_ = lean_box(0);
v_cs_1297_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1292_, v___x_1296_);
v___x_1301_ = l_List_isEmpty___redArg(v_cs_1297_);
if (v___x_1301_ == 0)
{
lean_dec(v_n_1291_);
goto v___jp_1298_;
}
else
{
lean_object* v_ref_1302_; lean_object* v___x_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_cs_1297_);
v_ref_1302_ = lean_ctor_get(v___y_1293_, 5);
v___x_1303_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1302_, v_n_1291_, v___y_1293_, v___y_1294_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1297_, v___x_1296_);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1312_, lean_object* v_cs_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1312_, v_cs_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; 
lean_inc(v_n_1318_);
v___x_1322_ = l_Lean_realizeGlobalName(v_n_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1318_, v_a_1323_, v_a_1319_, v_a_1320_);
return v___x_1324_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_n_1318_);
v_a_1325_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1322_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_realizeGlobalConstCore(v_n_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1338_, lean_object* v_ref_1339_, lean_object* v_constName_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1339_, v_constName_1340_, v___y_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_ref_1346_, lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1345_, v_ref_1346_, v_constName_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v_ref_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1352_, lean_object* v_ref_1353_, lean_object* v_msg_1354_, lean_object* v_declHint_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1353_, v_msg_1354_, v_declHint_1355_, v___y_1356_, v___y_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_ref_1361_, lean_object* v_msg_1362_, lean_object* v_declHint_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1360_, v_ref_1361_, v_msg_1362_, v_declHint_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v_ref_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1368_, lean_object* v_declHint_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1368_, v_declHint_1369_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1374_, lean_object* v_declHint_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1374_, v_declHint_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1380_, lean_object* v_ref_1381_, lean_object* v_msg_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1381_, v_msg_1382_, v___y_1383_, v___y_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1387_, lean_object* v_ref_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1387_, v_ref_1388_, v_msg_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v_ref_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1400_, v_msg_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
if (lean_obj_tag(v_a_1406_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = l_List_reverse___redArg(v_a_1407_);
return v___x_1408_;
}
else
{
lean_object* v_head_1409_; lean_object* v_tail_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1419_; 
v_head_1409_ = lean_ctor_get(v_a_1406_, 0);
v_tail_1410_ = lean_ctor_get(v_a_1406_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1412_ = v_a_1406_;
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_tail_1410_);
lean_inc(v_head_1409_);
lean_dec(v_a_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = l_Lean_MessageData_ofExpr(v_head_1409_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_a_1407_);
lean_ctor_set(v___x_1412_, 0, v___x_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1407_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v_a_1406_ = v_tail_1410_;
v_a_1407_ = v___x_1416_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
if (lean_obj_tag(v_a_1420_) == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = l_List_reverse___redArg(v_a_1421_);
return v___x_1422_;
}
else
{
lean_object* v_head_1423_; lean_object* v_tail_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1434_; 
v_head_1423_ = lean_ctor_get(v_a_1420_, 0);
v_tail_1424_ = lean_ctor_get(v_a_1420_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_a_1420_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1426_ = v_a_1420_;
v_isShared_1427_ = v_isSharedCheck_1434_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_tail_1424_);
lean_inc(v_head_1423_);
lean_dec(v_a_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1434_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Lean_mkConst(v_head_1423_, v___x_1428_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_a_1421_);
lean_ctor_set(v___x_1426_, 0, v___x_1429_);
v___x_1431_ = v___x_1426_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_a_1421_);
v___x_1431_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
v_a_1420_ = v_tail_1424_;
v_a_1421_ = v___x_1431_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1440_ = l_Lean_stringToMessageData(v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1441_, lean_object* v_cs_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
if (lean_obj_tag(v_cs_1442_) == 1)
{
lean_object* v_tail_1458_; 
v_tail_1458_ = lean_ctor_get(v_cs_1442_, 1);
if (lean_obj_tag(v_tail_1458_) == 0)
{
lean_object* v_head_1459_; lean_object* v___x_1460_; 
lean_dec(v_n_1441_);
v_head_1459_ = lean_ctor_get(v_cs_1442_, 0);
lean_inc(v_head_1459_);
lean_dec_ref(v_cs_1442_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_head_1459_);
return v___x_1460_;
}
else
{
goto v___jp_1446_;
}
}
else
{
goto v___jp_1446_;
}
v___jp_1446_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1447_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1448_ = l_Lean_MessageData_ofName(v_n_1441_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_box(0);
v___x_1453_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1442_, v___x_1452_);
v___x_1454_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1453_, v___x_1452_);
v___x_1455_ = l_Lean_MessageData_ofList(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1451_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1456_, v___y_1443_, v___y_1444_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1461_, lean_object* v_cs_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1461_, v_cs_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1471_; 
lean_inc(v_n_1467_);
v___x_1471_ = l_Lean_realizeGlobalConstCore(v_n_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1467_, v_a_1472_, v_a_1468_, v_a_1469_);
return v___x_1473_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_n_1467_);
v_a_1474_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1471_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1471_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
if (lean_obj_tag(v_a_1487_) == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_array_to_list(v_a_1488_);
return v___x_1489_;
}
else
{
lean_object* v_head_1490_; 
v_head_1490_ = lean_ctor_get(v_a_1487_, 0);
if (lean_obj_tag(v_head_1490_) == 1)
{
lean_object* v_fields_1491_; 
v_fields_1491_ = lean_ctor_get(v_head_1490_, 1);
if (lean_obj_tag(v_fields_1491_) == 0)
{
lean_object* v_tail_1492_; lean_object* v_n_1493_; lean_object* v___x_1494_; 
lean_inc_ref(v_head_1490_);
v_tail_1492_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_tail_1492_);
lean_dec_ref(v_a_1487_);
v_n_1493_ = lean_ctor_get(v_head_1490_, 0);
lean_inc(v_n_1493_);
lean_dec_ref(v_head_1490_);
v___x_1494_ = lean_array_push(v_a_1488_, v_n_1493_);
v_a_1487_ = v_tail_1492_;
v_a_1488_ = v___x_1494_;
goto _start;
}
else
{
lean_object* v_tail_1496_; 
v_tail_1496_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_tail_1496_);
lean_dec_ref(v_a_1487_);
v_a_1487_ = v_tail_1496_;
goto _start;
}
}
else
{
lean_object* v_tail_1498_; 
v_tail_1498_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_tail_1498_);
lean_dec_ref(v_a_1487_);
v_a_1487_ = v_tail_1498_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1506_ = l_Lean_MessageData_ofFormat(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1507_, lean_object* v_k_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
if (lean_obj_tag(v_stx_1507_) == 3)
{
lean_object* v_val_1512_; lean_object* v_preresolved_1513_; lean_object* v___x_1514_; lean_object* v_pre_1515_; uint8_t v___x_1516_; 
v_val_1512_ = lean_ctor_get(v_stx_1507_, 2);
lean_inc(v_val_1512_);
v_preresolved_1513_ = lean_ctor_get(v_stx_1507_, 3);
v___x_1514_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1513_);
v_pre_1515_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1513_, v___x_1514_);
v___x_1516_ = l_List_isEmpty___redArg(v_pre_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_stx_1507_);
lean_dec(v_val_1512_);
lean_dec_ref(v_k_1508_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_pre_1515_);
return v___x_1517_;
}
else
{
lean_object* v_fileName_1518_; lean_object* v_fileMap_1519_; lean_object* v_options_1520_; lean_object* v_currRecDepth_1521_; lean_object* v_maxRecDepth_1522_; lean_object* v_ref_1523_; lean_object* v_currNamespace_1524_; lean_object* v_openDecls_1525_; lean_object* v_initHeartbeats_1526_; lean_object* v_maxHeartbeats_1527_; lean_object* v_quotContext_1528_; lean_object* v_currMacroScope_1529_; uint8_t v_diag_1530_; lean_object* v_cancelTk_x3f_1531_; uint8_t v_suppressElabErrors_1532_; lean_object* v_inheritedTraceOptions_1533_; lean_object* v_ref_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_pre_1515_);
v_fileName_1518_ = lean_ctor_get(v___y_1509_, 0);
v_fileMap_1519_ = lean_ctor_get(v___y_1509_, 1);
v_options_1520_ = lean_ctor_get(v___y_1509_, 2);
v_currRecDepth_1521_ = lean_ctor_get(v___y_1509_, 3);
v_maxRecDepth_1522_ = lean_ctor_get(v___y_1509_, 4);
v_ref_1523_ = lean_ctor_get(v___y_1509_, 5);
v_currNamespace_1524_ = lean_ctor_get(v___y_1509_, 6);
v_openDecls_1525_ = lean_ctor_get(v___y_1509_, 7);
v_initHeartbeats_1526_ = lean_ctor_get(v___y_1509_, 8);
v_maxHeartbeats_1527_ = lean_ctor_get(v___y_1509_, 9);
v_quotContext_1528_ = lean_ctor_get(v___y_1509_, 10);
v_currMacroScope_1529_ = lean_ctor_get(v___y_1509_, 11);
v_diag_1530_ = lean_ctor_get_uint8(v___y_1509_, sizeof(void*)*14);
v_cancelTk_x3f_1531_ = lean_ctor_get(v___y_1509_, 12);
v_suppressElabErrors_1532_ = lean_ctor_get_uint8(v___y_1509_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1533_ = lean_ctor_get(v___y_1509_, 13);
v_ref_1534_ = l_Lean_replaceRef(v_stx_1507_, v_ref_1523_);
lean_dec_ref(v_stx_1507_);
lean_inc_ref(v_inheritedTraceOptions_1533_);
lean_inc(v_cancelTk_x3f_1531_);
lean_inc(v_currMacroScope_1529_);
lean_inc(v_quotContext_1528_);
lean_inc(v_maxHeartbeats_1527_);
lean_inc(v_initHeartbeats_1526_);
lean_inc(v_openDecls_1525_);
lean_inc(v_currNamespace_1524_);
lean_inc(v_maxRecDepth_1522_);
lean_inc(v_currRecDepth_1521_);
lean_inc_ref(v_options_1520_);
lean_inc_ref(v_fileMap_1519_);
lean_inc_ref(v_fileName_1518_);
v___x_1535_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1535_, 0, v_fileName_1518_);
lean_ctor_set(v___x_1535_, 1, v_fileMap_1519_);
lean_ctor_set(v___x_1535_, 2, v_options_1520_);
lean_ctor_set(v___x_1535_, 3, v_currRecDepth_1521_);
lean_ctor_set(v___x_1535_, 4, v_maxRecDepth_1522_);
lean_ctor_set(v___x_1535_, 5, v_ref_1534_);
lean_ctor_set(v___x_1535_, 6, v_currNamespace_1524_);
lean_ctor_set(v___x_1535_, 7, v_openDecls_1525_);
lean_ctor_set(v___x_1535_, 8, v_initHeartbeats_1526_);
lean_ctor_set(v___x_1535_, 9, v_maxHeartbeats_1527_);
lean_ctor_set(v___x_1535_, 10, v_quotContext_1528_);
lean_ctor_set(v___x_1535_, 11, v_currMacroScope_1529_);
lean_ctor_set(v___x_1535_, 12, v_cancelTk_x3f_1531_);
lean_ctor_set(v___x_1535_, 13, v_inheritedTraceOptions_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*14, v_diag_1530_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*14 + 1, v_suppressElabErrors_1532_);
lean_inc(v___y_1510_);
v___x_1536_ = lean_apply_4(v_k_1508_, v_val_1512_, v___x_1535_, v___y_1510_, lean_box(0));
return v___x_1536_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v_k_1508_);
v___x_1537_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1538_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1507_, v___x_1537_, v___y_1509_, v___y_1510_);
lean_dec(v_stx_1507_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1539_, lean_object* v_k_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1539_, v_k_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_fileName_1550_; lean_object* v_fileMap_1551_; lean_object* v_options_1552_; lean_object* v_currRecDepth_1553_; lean_object* v_maxRecDepth_1554_; lean_object* v_ref_1555_; lean_object* v_currNamespace_1556_; lean_object* v_openDecls_1557_; lean_object* v_initHeartbeats_1558_; lean_object* v_maxHeartbeats_1559_; lean_object* v_quotContext_1560_; lean_object* v_currMacroScope_1561_; uint8_t v_diag_1562_; lean_object* v_cancelTk_x3f_1563_; uint8_t v_suppressElabErrors_1564_; lean_object* v_inheritedTraceOptions_1565_; lean_object* v___x_1566_; lean_object* v_ref_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_fileName_1550_ = lean_ctor_get(v_a_1547_, 0);
v_fileMap_1551_ = lean_ctor_get(v_a_1547_, 1);
v_options_1552_ = lean_ctor_get(v_a_1547_, 2);
v_currRecDepth_1553_ = lean_ctor_get(v_a_1547_, 3);
v_maxRecDepth_1554_ = lean_ctor_get(v_a_1547_, 4);
v_ref_1555_ = lean_ctor_get(v_a_1547_, 5);
v_currNamespace_1556_ = lean_ctor_get(v_a_1547_, 6);
v_openDecls_1557_ = lean_ctor_get(v_a_1547_, 7);
v_initHeartbeats_1558_ = lean_ctor_get(v_a_1547_, 8);
v_maxHeartbeats_1559_ = lean_ctor_get(v_a_1547_, 9);
v_quotContext_1560_ = lean_ctor_get(v_a_1547_, 10);
v_currMacroScope_1561_ = lean_ctor_get(v_a_1547_, 11);
v_diag_1562_ = lean_ctor_get_uint8(v_a_1547_, sizeof(void*)*14);
v_cancelTk_x3f_1563_ = lean_ctor_get(v_a_1547_, 12);
v_suppressElabErrors_1564_ = lean_ctor_get_uint8(v_a_1547_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1565_ = lean_ctor_get(v_a_1547_, 13);
v___x_1566_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1567_ = l_Lean_replaceRef(v_stx_1546_, v_ref_1555_);
lean_inc_ref(v_inheritedTraceOptions_1565_);
lean_inc(v_cancelTk_x3f_1563_);
lean_inc(v_currMacroScope_1561_);
lean_inc(v_quotContext_1560_);
lean_inc(v_maxHeartbeats_1559_);
lean_inc(v_initHeartbeats_1558_);
lean_inc(v_openDecls_1557_);
lean_inc(v_currNamespace_1556_);
lean_inc(v_maxRecDepth_1554_);
lean_inc(v_currRecDepth_1553_);
lean_inc_ref(v_options_1552_);
lean_inc_ref(v_fileMap_1551_);
lean_inc_ref(v_fileName_1550_);
v___x_1568_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1568_, 0, v_fileName_1550_);
lean_ctor_set(v___x_1568_, 1, v_fileMap_1551_);
lean_ctor_set(v___x_1568_, 2, v_options_1552_);
lean_ctor_set(v___x_1568_, 3, v_currRecDepth_1553_);
lean_ctor_set(v___x_1568_, 4, v_maxRecDepth_1554_);
lean_ctor_set(v___x_1568_, 5, v_ref_1567_);
lean_ctor_set(v___x_1568_, 6, v_currNamespace_1556_);
lean_ctor_set(v___x_1568_, 7, v_openDecls_1557_);
lean_ctor_set(v___x_1568_, 8, v_initHeartbeats_1558_);
lean_ctor_set(v___x_1568_, 9, v_maxHeartbeats_1559_);
lean_ctor_set(v___x_1568_, 10, v_quotContext_1560_);
lean_ctor_set(v___x_1568_, 11, v_currMacroScope_1561_);
lean_ctor_set(v___x_1568_, 12, v_cancelTk_x3f_1563_);
lean_ctor_set(v___x_1568_, 13, v_inheritedTraceOptions_1565_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*14, v_diag_1562_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*14 + 1, v_suppressElabErrors_1564_);
v___x_1569_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1546_, v___x_1566_, v___x_1568_, v_a_1548_);
lean_dec_ref(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_realizeGlobalConst(v_stx_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1574_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_instMonadEIO(lean_box(0));
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_toApplicative_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1615_; 
v___x_1582_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1583_ = l_StateRefT_x27_instMonad___redArg(v___x_1582_);
v_toApplicative_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1583_, 1);
lean_dec(v_unused_1616_);
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1615_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_toApplicative_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1615_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_toFunctor_1588_; lean_object* v_toSeq_1589_; lean_object* v_toSeqLeft_1590_; lean_object* v_toSeqRight_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1613_; 
v_toFunctor_1588_ = lean_ctor_get(v_toApplicative_1584_, 0);
v_toSeq_1589_ = lean_ctor_get(v_toApplicative_1584_, 2);
v_toSeqLeft_1590_ = lean_ctor_get(v_toApplicative_1584_, 3);
v_toSeqRight_1591_ = lean_ctor_get(v_toApplicative_1584_, 4);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_toApplicative_1584_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_toApplicative_1584_, 1);
lean_dec(v_unused_1614_);
v___x_1593_ = v_toApplicative_1584_;
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_toSeqRight_1591_);
lean_inc(v_toSeqLeft_1590_);
lean_inc(v_toSeq_1589_);
lean_inc(v_toFunctor_1588_);
lean_dec(v_toApplicative_1584_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___f_1602_; lean_object* v___x_1604_; 
v___f_1595_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1596_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1588_);
v___f_1597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1597_, 0, v_toFunctor_1588_);
v___f_1598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1598_, 0, v_toFunctor_1588_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___f_1597_);
lean_ctor_set(v___x_1599_, 1, v___f_1598_);
v___f_1600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1600_, 0, v_toSeqRight_1591_);
v___f_1601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1601_, 0, v_toSeqLeft_1590_);
v___f_1602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1602_, 0, v_toSeq_1589_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v___f_1600_);
lean_ctor_set(v___x_1593_, 3, v___f_1601_);
lean_ctor_set(v___x_1593_, 2, v___f_1602_);
lean_ctor_set(v___x_1593_, 1, v___f_1595_);
lean_ctor_set(v___x_1593_, 0, v___x_1599_);
v___x_1604_ = v___x_1593_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___f_1595_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v___f_1602_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___f_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___f_1600_);
v___x_1604_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___f_1596_);
lean_ctor_set(v___x_1586_, 0, v___x_1604_);
v___x_1606_ = v___x_1586_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___f_1596_);
v___x_1606_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_195__overap_1609_; lean_object* v___x_1610_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = l_instInhabitedOfMonad___redArg(v___x_1606_, v___x_1607_);
v___x_195__overap_1609_ = lean_panic_fn_borrowed(v___x_1608_, v_msg_1578_);
lean_dec(v___x_1608_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
v___x_1610_ = lean_apply_3(v___x_195__overap_1609_, v___y_1579_, v___y_1580_, lean_box(0));
return v___x_1610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
return v_x_1623_;
}
else
{
lean_object* v_head_1625_; lean_object* v_tail_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_head_1625_ = lean_ctor_get(v_x_1624_, 0);
v_tail_1626_ = lean_ctor_get(v_x_1624_, 1);
v___x_1627_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1628_ = lean_string_append(v_x_1623_, v___x_1627_);
v___x_1629_ = lean_expr_dbg_to_string(v_head_1625_);
v___x_1630_ = lean_string_append(v___x_1628_, v___x_1629_);
lean_dec_ref(v___x_1629_);
v_x_1623_ = v___x_1630_;
v_x_1624_ = v_tail_1626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1632_, v_x_1633_);
lean_dec(v_x_1633_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1639_;
}
else
{
lean_object* v_tail_1640_; 
v_tail_1640_ = lean_ctor_get(v_x_1638_, 1);
if (lean_obj_tag(v_tail_1640_) == 0)
{
lean_object* v_head_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_head_1641_ = lean_ctor_get(v_x_1638_, 0);
v___x_1642_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1643_ = lean_expr_dbg_to_string(v_head_1641_);
v___x_1644_ = lean_string_append(v___x_1642_, v___x_1643_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1646_ = lean_string_append(v___x_1644_, v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v_head_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; uint32_t v___x_1652_; lean_object* v___x_1653_; 
v_head_1647_ = lean_ctor_get(v_x_1638_, 0);
v___x_1648_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1649_ = lean_expr_dbg_to_string(v_head_1647_);
v___x_1650_ = lean_string_append(v___x_1648_, v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1650_, v_tail_1640_);
v___x_1652_ = 93;
v___x_1653_ = lean_string_push(v___x_1651_, v___x_1652_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1654_);
lean_dec(v_x_1654_);
return v_res_1655_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1659_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1660_ = lean_unsigned_to_nat(11u);
v___x_1661_ = lean_unsigned_to_nat(429u);
v___x_1662_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1663_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1664_ = l_mkPanicMessageWithDecl(v___x_1663_, v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1667_, lean_object* v_cs_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
if (lean_obj_tag(v_cs_1668_) == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_id_1667_);
v___x_1672_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1673_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1672_, v___y_1669_, v___y_1670_);
return v___x_1673_;
}
else
{
lean_object* v_tail_1674_; 
v_tail_1674_ = lean_ctor_get(v_cs_1668_, 1);
if (lean_obj_tag(v_tail_1674_) == 0)
{
lean_object* v_head_1675_; lean_object* v___x_1676_; 
lean_dec(v_id_1667_);
v_head_1675_ = lean_ctor_get(v_cs_1668_, 0);
lean_inc(v_head_1675_);
lean_dec_ref(v_cs_1668_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_head_1675_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1677_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1678_ = lean_box(0);
v___x_1679_ = 0;
lean_inc(v_id_1667_);
v___x_1680_ = l_Lean_Syntax_formatStx(v_id_1667_, v___x_1678_, v___x_1679_);
v___x_1681_ = l_Std_Format_defWidth;
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = l_Std_Format_pretty(v___x_1680_, v___x_1681_, v___x_1682_, v___x_1682_);
v___x_1684_ = lean_string_append(v___x_1677_, v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1686_ = lean_string_append(v___x_1684_, v___x_1685_);
v___x_1687_ = lean_box(0);
v___x_1688_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1668_, v___x_1687_);
v___x_1689_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1688_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_string_append(v___x_1686_, v___x_1689_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
v___x_1692_ = l_Lean_MessageData_ofFormat(v___x_1691_);
v___x_1693_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1667_, v___x_1692_, v___y_1669_, v___y_1670_);
lean_dec(v_id_1667_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1694_, lean_object* v_cs_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1694_, v_cs_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
lean_inc(v_id_1700_);
v___x_1704_ = l_Lean_realizeGlobalConst(v_id_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1700_, v_a_1705_, v_a_1701_, v_a_1702_);
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_id_1700_);
v_a_1707_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1704_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_realizeGlobalConstNoOverload(v_id_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1719_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_unsigned_to_nat(3863082579u);
v___x_1752_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1753_ = l_Lean_Name_num___override(v___x_1752_, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1756_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1757_ = l_Lean_Name_str___override(v___x_1756_, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1760_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1761_ = l_Lean_Name_str___override(v___x_1760_, v___x_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = lean_unsigned_to_nat(2u);
v___x_1763_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1764_ = l_Lean_Name_num___override(v___x_1763_, v___x_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1766_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1767_ = 0;
v___x_1768_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1769_ = l_Lean_registerTraceClass(v___x_1766_, v___x_1767_, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1771_;
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

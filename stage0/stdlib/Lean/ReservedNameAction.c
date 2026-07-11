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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "executeReservedNameAction for "};
static const lean_object* l_Lean_executeReservedNameAction___lam__0___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_executeReservedNameAction___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_executeReservedNameAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l_Lean_executeReservedNameAction___closed__0 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__0_value;
static const lean_ctor_object l_Lean_executeReservedNameAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_executeReservedNameAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l_Lean_executeReservedNameAction___closed__1 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__1_value;
static const lean_string_object l_Lean_executeReservedNameAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_executeReservedNameAction___closed__2 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__2_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_executeReservedNameAction___closed__3;
static const lean_string_object l_Lean_executeReservedNameAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_executeReservedNameAction___closed__4 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__4_value;
static const lean_ctor_object l_Lean_executeReservedNameAction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_executeReservedNameAction___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_executeReservedNameAction___closed__5 = (const lean_object*)&l_Lean_executeReservedNameAction___closed__5_value;
static lean_once_cell_t l_Lean_executeReservedNameAction___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_executeReservedNameAction___closed__6;
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((size_t)5ULL);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__0);
v___x_51_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_47_);
lean_ctor_set(v___x_51_, 3, v___x_47_);
lean_ctor_set_usize(v___x_51_, 4, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg(lean_object* v___y_52_){
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
v___x_74_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg___boxed(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg(v___y_86_);
lean_dec(v___y_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0(lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg(v___y_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0(v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(lean_object* v_opts_97_, lean_object* v_opt_98_){
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
lean_dec_ref_known(v___x_102_, 1);
if (lean_obj_tag(v_val_104_) == 1)
{
uint8_t v_v_105_; 
v_v_105_ = lean_ctor_get_uint8(v_val_104_, 0);
lean_dec_ref_known(v_val_104_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v_opts_107_, lean_object* v_opt_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_opts_107_, v_opt_108_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4(lean_object* v_e_129_){
_start:
{
if (lean_obj_tag(v_e_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 2;
return v___x_130_;
}
else
{
lean_object* v_a_131_; uint8_t v___x_132_; 
v_a_131_ = lean_ctor_get(v_e_129_, 0);
v___x_132_ = lean_unbox(v_a_131_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4___boxed(lean_object* v_e_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4(v_e_135_);
lean_dec_ref(v_e_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v_x_138_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v_x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 1);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v_x_138_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v_x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set_tag(v___x_150_, 0);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg___boxed(lean_object* v_x_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(v_x_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5(lean_object* v_opts_159_, lean_object* v_opt_160_){
_start:
{
lean_object* v_name_161_; lean_object* v_defValue_162_; lean_object* v_map_163_; lean_object* v___x_164_; 
v_name_161_ = lean_ctor_get(v_opt_160_, 0);
v_defValue_162_ = lean_ctor_get(v_opt_160_, 1);
v_map_163_ = lean_ctor_get(v_opts_159_, 0);
v___x_164_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_163_, v_name_161_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_inc(v_defValue_162_);
return v_defValue_162_;
}
else
{
lean_object* v_val_165_; 
v_val_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_164_, 1);
if (lean_obj_tag(v_val_165_) == 3)
{
lean_object* v_v_166_; 
v_v_166_ = lean_ctor_get(v_val_165_, 0);
lean_inc(v_v_166_);
lean_dec_ref_known(v_val_165_, 1);
return v_v_166_;
}
else
{
lean_dec(v_val_165_);
lean_inc(v_defValue_162_);
return v_defValue_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5___boxed(lean_object* v_opts_167_, lean_object* v_opt_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5(v_opts_167_, v_opt_168_);
lean_dec_ref(v_opt_168_);
lean_dec_ref(v_opts_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3(size_t v_sz_170_, size_t v_i_171_, lean_object* v_bs_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_lt(v_i_171_, v_sz_170_);
if (v___x_173_ == 0)
{
return v_bs_172_;
}
else
{
lean_object* v_v_174_; lean_object* v_msg_175_; lean_object* v___x_176_; lean_object* v_bs_x27_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v_v_174_ = lean_array_uget_borrowed(v_bs_172_, v_i_171_);
v_msg_175_ = lean_ctor_get(v_v_174_, 1);
lean_inc_ref(v_msg_175_);
v___x_176_ = lean_unsigned_to_nat(0u);
v_bs_x27_177_ = lean_array_uset(v_bs_172_, v_i_171_, v___x_176_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_171_, v___x_178_);
v___x_180_ = lean_array_uset(v_bs_x27_177_, v_i_171_, v_msg_175_);
v_i_171_ = v___x_179_;
v_bs_172_ = v___x_180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_182_, lean_object* v_i_183_, lean_object* v_bs_184_){
_start:
{
size_t v_sz_boxed_185_; size_t v_i_boxed_186_; lean_object* v_res_187_; 
v_sz_boxed_185_ = lean_unbox_usize(v_sz_182_);
lean_dec(v_sz_182_);
v_i_boxed_186_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3(v_sz_boxed_185_, v_i_boxed_186_, v_bs_184_);
return v_res_187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_188_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__0);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
lean_ctor_set(v___x_193_, 3, v___x_192_);
lean_ctor_set(v___x_193_, 4, v___x_191_);
lean_ctor_set(v___x_193_, 5, v___x_191_);
lean_ctor_set(v___x_193_, 6, v___x_191_);
lean_ctor_set(v___x_193_, 7, v___x_191_);
lean_ctor_set(v___x_193_, 8, v___x_191_);
lean_ctor_set(v___x_193_, 9, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_unsigned_to_nat(32u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4(void){
_start:
{
size_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_197_ = ((size_t)5ULL);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_unsigned_to_nat(32u);
v___x_200_ = lean_mk_empty_array_with_capacity(v___x_199_);
v___x_201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__3);
v___x_202_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_198_);
lean_ctor_set(v___x_202_, 3, v___x_198_);
lean_ctor_set_usize(v___x_202_, 4, v___x_197_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_box(1);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__4);
v___x_205_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__1);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_env_212_; lean_object* v_options_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_211_ = lean_st_ref_get(v___y_209_);
v_env_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_env_212_);
lean_dec(v___x_211_);
v_options_213_ = lean_ctor_get(v___y_208_, 2);
v___x_214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2);
v___x_215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5);
lean_inc_ref(v_options_213_);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v_env_212_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_215_);
lean_ctor_set(v___x_216_, 3, v_options_213_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_msgData_207_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(v_msgData_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2(lean_object* v_oldTraces_224_, lean_object* v_data_225_, lean_object* v_ref_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_fileName_231_; lean_object* v_fileMap_232_; lean_object* v_options_233_; lean_object* v_currRecDepth_234_; lean_object* v_maxRecDepth_235_; lean_object* v_ref_236_; lean_object* v_currNamespace_237_; lean_object* v_openDecls_238_; lean_object* v_initHeartbeats_239_; lean_object* v_maxHeartbeats_240_; lean_object* v_quotContext_241_; lean_object* v_currMacroScope_242_; uint8_t v_diag_243_; lean_object* v_cancelTk_x3f_244_; uint8_t v_suppressElabErrors_245_; lean_object* v_inheritedTraceOptions_246_; lean_object* v___x_247_; lean_object* v_traceState_248_; lean_object* v_traces_249_; lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v___x_252_; size_t v_sz_253_; size_t v___x_254_; lean_object* v___x_255_; lean_object* v_msg_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_295_; 
v_fileName_231_ = lean_ctor_get(v___y_228_, 0);
v_fileMap_232_ = lean_ctor_get(v___y_228_, 1);
v_options_233_ = lean_ctor_get(v___y_228_, 2);
v_currRecDepth_234_ = lean_ctor_get(v___y_228_, 3);
v_maxRecDepth_235_ = lean_ctor_get(v___y_228_, 4);
v_ref_236_ = lean_ctor_get(v___y_228_, 5);
v_currNamespace_237_ = lean_ctor_get(v___y_228_, 6);
v_openDecls_238_ = lean_ctor_get(v___y_228_, 7);
v_initHeartbeats_239_ = lean_ctor_get(v___y_228_, 8);
v_maxHeartbeats_240_ = lean_ctor_get(v___y_228_, 9);
v_quotContext_241_ = lean_ctor_get(v___y_228_, 10);
v_currMacroScope_242_ = lean_ctor_get(v___y_228_, 11);
v_diag_243_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*14);
v_cancelTk_x3f_244_ = lean_ctor_get(v___y_228_, 12);
v_suppressElabErrors_245_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_246_ = lean_ctor_get(v___y_228_, 13);
v___x_247_ = lean_st_ref_get(v___y_229_);
v_traceState_248_ = lean_ctor_get(v___x_247_, 4);
lean_inc_ref(v_traceState_248_);
lean_dec(v___x_247_);
v_traces_249_ = lean_ctor_get(v_traceState_248_, 0);
lean_inc_ref(v_traces_249_);
lean_dec_ref(v_traceState_248_);
v_ref_250_ = l_Lean_replaceRef(v_ref_226_, v_ref_236_);
lean_inc_ref(v_inheritedTraceOptions_246_);
lean_inc(v_cancelTk_x3f_244_);
lean_inc(v_currMacroScope_242_);
lean_inc(v_quotContext_241_);
lean_inc(v_maxHeartbeats_240_);
lean_inc(v_initHeartbeats_239_);
lean_inc(v_openDecls_238_);
lean_inc(v_currNamespace_237_);
lean_inc(v_maxRecDepth_235_);
lean_inc(v_currRecDepth_234_);
lean_inc_ref(v_options_233_);
lean_inc_ref(v_fileMap_232_);
lean_inc_ref(v_fileName_231_);
v___x_251_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_251_, 0, v_fileName_231_);
lean_ctor_set(v___x_251_, 1, v_fileMap_232_);
lean_ctor_set(v___x_251_, 2, v_options_233_);
lean_ctor_set(v___x_251_, 3, v_currRecDepth_234_);
lean_ctor_set(v___x_251_, 4, v_maxRecDepth_235_);
lean_ctor_set(v___x_251_, 5, v_ref_250_);
lean_ctor_set(v___x_251_, 6, v_currNamespace_237_);
lean_ctor_set(v___x_251_, 7, v_openDecls_238_);
lean_ctor_set(v___x_251_, 8, v_initHeartbeats_239_);
lean_ctor_set(v___x_251_, 9, v_maxHeartbeats_240_);
lean_ctor_set(v___x_251_, 10, v_quotContext_241_);
lean_ctor_set(v___x_251_, 11, v_currMacroScope_242_);
lean_ctor_set(v___x_251_, 12, v_cancelTk_x3f_244_);
lean_ctor_set(v___x_251_, 13, v_inheritedTraceOptions_246_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*14, v_diag_243_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*14 + 1, v_suppressElabErrors_245_);
v___x_252_ = l_Lean_PersistentArray_toArray___redArg(v_traces_249_);
lean_dec_ref(v_traces_249_);
v_sz_253_ = lean_array_size(v___x_252_);
v___x_254_ = ((size_t)0ULL);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__3(v_sz_253_, v___x_254_, v___x_252_);
v_msg_256_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_256_, 0, v_data_225_);
lean_ctor_set(v_msg_256_, 1, v_msg_227_);
lean_ctor_set(v_msg_256_, 2, v___x_255_);
v___x_257_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(v_msg_256_, v___x_251_, v___y_229_);
lean_dec_ref_known(v___x_251_, 14);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_295_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_295_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_295_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v_traceState_263_; lean_object* v_env_264_; lean_object* v_nextMacroScope_265_; lean_object* v_ngen_266_; lean_object* v_auxDeclNGen_267_; lean_object* v_cache_268_; lean_object* v_messages_269_; lean_object* v_infoState_270_; lean_object* v_snapshotTasks_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v___x_262_ = lean_st_ref_take(v___y_229_);
v_traceState_263_ = lean_ctor_get(v___x_262_, 4);
v_env_264_ = lean_ctor_get(v___x_262_, 0);
v_nextMacroScope_265_ = lean_ctor_get(v___x_262_, 1);
v_ngen_266_ = lean_ctor_get(v___x_262_, 2);
v_auxDeclNGen_267_ = lean_ctor_get(v___x_262_, 3);
v_cache_268_ = lean_ctor_get(v___x_262_, 5);
v_messages_269_ = lean_ctor_get(v___x_262_, 6);
v_infoState_270_ = lean_ctor_get(v___x_262_, 7);
v_snapshotTasks_271_ = lean_ctor_get(v___x_262_, 8);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v___x_262_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snapshotTasks_271_);
lean_inc(v_infoState_270_);
lean_inc(v_messages_269_);
lean_inc(v_cache_268_);
lean_inc(v_traceState_263_);
lean_inc(v_auxDeclNGen_267_);
lean_inc(v_ngen_266_);
lean_inc(v_nextMacroScope_265_);
lean_inc(v_env_264_);
lean_dec(v___x_262_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint64_t v_tid_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_292_; 
v_tid_275_ = lean_ctor_get_uint64(v_traceState_263_, sizeof(void*)*1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_traceState_263_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_traceState_263_, 0);
lean_dec(v_unused_293_);
v___x_277_ = v_traceState_263_;
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
else
{
lean_dec(v_traceState_263_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_ref_226_);
lean_ctor_set(v___x_279_, 1, v_a_258_);
v___x_280_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_224_, v___x_279_);
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
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_env_264_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_nextMacroScope_265_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_ngen_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_auxDeclNGen_267_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_cache_268_);
lean_ctor_set(v_reuseFailAlloc_290_, 6, v_messages_269_);
lean_ctor_set(v_reuseFailAlloc_290_, 7, v_infoState_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 8, v_snapshotTasks_271_);
v___x_284_ = v_reuseFailAlloc_290_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = lean_st_ref_set(v___y_229_, v___x_284_);
v___x_286_ = lean_box(0);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_286_);
v___x_288_ = v___x_260_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2___boxed(lean_object* v_oldTraces_296_, lean_object* v_data_297_, lean_object* v_ref_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2(v_oldTraces_296_, v_data_297_, v_ref_298_, v_msg_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0(void){
_start:
{
lean_object* v___x_304_; double v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_float_of_nat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__1));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3(void){
_start:
{
lean_object* v___x_309_; double v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1000u);
v___x_310_ = lean_float_of_nat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2(lean_object* v_cls_311_, uint8_t v_collapsed_312_, lean_object* v_tag_313_, lean_object* v_opts_314_, uint8_t v_clsEnabled_315_, lean_object* v_oldTraces_316_, lean_object* v_msg_317_, lean_object* v_resStartStop_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v_data_327_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___y_343_; lean_object* v_a_344_; uint8_t v___y_359_; double v___y_390_; 
v_fst_322_ = lean_ctor_get(v_resStartStop_318_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v_resStartStop_318_, 1);
lean_inc(v_snd_323_);
lean_dec_ref(v_resStartStop_318_);
v_fst_338_ = lean_ctor_get(v_snd_323_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_snd_323_, 1);
lean_inc(v_snd_339_);
lean_dec(v_snd_323_);
v___x_340_ = l_Lean_trace_profiler;
v___x_341_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_opts_314_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_359_ = v___x_341_;
goto v___jp_358_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_trace_profiler_useHeartbeats;
v___x_396_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_opts_314_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; double v___x_399_; double v___x_400_; double v___x_401_; 
v___x_397_ = l_Lean_trace_profiler_threshold;
v___x_398_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5(v_opts_314_, v___x_397_);
v___x_399_ = lean_float_of_nat(v___x_398_);
v___x_400_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__3);
v___x_401_ = lean_float_div(v___x_399_, v___x_400_);
v___y_390_ = v___x_401_;
goto v___jp_389_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; double v___x_404_; 
v___x_402_ = l_Lean_trace_profiler_threshold;
v___x_403_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__5(v_opts_314_, v___x_402_);
v___x_404_ = lean_float_of_nat(v___x_403_);
v___y_390_ = v___x_404_;
goto v___jp_389_;
}
}
v___jp_324_:
{
lean_object* v___x_328_; 
lean_inc(v___y_325_);
v___x_328_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2(v_oldTraces_316_, v_data_327_, v___y_325_, v___y_326_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(v_fst_322_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_fst_322_);
v_a_330_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_342_:
{
uint8_t v_result_345_; lean_object* v___x_346_; lean_object* v___x_347_; double v___x_348_; lean_object* v_data_349_; 
v_result_345_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__4(v_fst_322_);
v___x_346_ = lean_box(v_result_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__0);
lean_inc_ref(v_tag_313_);
lean_inc_ref(v___x_347_);
lean_inc(v_cls_311_);
v_data_349_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_349_, 0, v_cls_311_);
lean_ctor_set(v_data_349_, 1, v___x_347_);
lean_ctor_set(v_data_349_, 2, v_tag_313_);
lean_ctor_set_float(v_data_349_, sizeof(void*)*3, v___x_348_);
lean_ctor_set_float(v_data_349_, sizeof(void*)*3 + 8, v___x_348_);
lean_ctor_set_uint8(v_data_349_, sizeof(void*)*3 + 16, v_collapsed_312_);
if (v___x_341_ == 0)
{
lean_dec_ref_known(v___x_347_, 1);
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
lean_dec_ref(v_tag_313_);
lean_dec(v_cls_311_);
v___y_325_ = v___y_343_;
v___y_326_ = v_a_344_;
v_data_327_ = v_data_349_;
goto v___jp_324_;
}
else
{
lean_object* v_data_350_; double v___x_351_; double v___x_352_; 
lean_dec_ref_known(v_data_349_, 3);
v_data_350_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_350_, 0, v_cls_311_);
lean_ctor_set(v_data_350_, 1, v___x_347_);
lean_ctor_set(v_data_350_, 2, v_tag_313_);
v___x_351_ = lean_unbox_float(v_fst_338_);
lean_dec(v_fst_338_);
lean_ctor_set_float(v_data_350_, sizeof(void*)*3, v___x_351_);
v___x_352_ = lean_unbox_float(v_snd_339_);
lean_dec(v_snd_339_);
lean_ctor_set_float(v_data_350_, sizeof(void*)*3 + 8, v___x_352_);
lean_ctor_set_uint8(v_data_350_, sizeof(void*)*3 + 16, v_collapsed_312_);
v___y_325_ = v___y_343_;
v___y_326_ = v_a_344_;
v_data_327_ = v_data_350_;
goto v___jp_324_;
}
}
v___jp_353_:
{
lean_object* v_ref_354_; lean_object* v___x_355_; 
v_ref_354_ = lean_ctor_get(v___y_319_, 5);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v_fst_322_);
v___x_355_ = lean_apply_4(v_msg_317_, v_fst_322_, v___y_319_, v___y_320_, lean_box(0));
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___y_343_ = v_ref_354_;
v_a_344_ = v_a_356_;
goto v___jp_342_;
}
else
{
lean_object* v___x_357_; 
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___closed__2);
v___y_343_ = v_ref_354_;
v_a_344_ = v___x_357_;
goto v___jp_342_;
}
}
v___jp_358_:
{
if (v_clsEnabled_315_ == 0)
{
if (v___y_359_ == 0)
{
lean_object* v___x_360_; lean_object* v_traceState_361_; lean_object* v_env_362_; lean_object* v_nextMacroScope_363_; lean_object* v_ngen_364_; lean_object* v_auxDeclNGen_365_; lean_object* v_cache_366_; lean_object* v_messages_367_; lean_object* v_infoState_368_; lean_object* v_snapshotTasks_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
lean_dec_ref(v_msg_317_);
lean_dec_ref(v_tag_313_);
lean_dec(v_cls_311_);
v___x_360_ = lean_st_ref_take(v___y_320_);
v_traceState_361_ = lean_ctor_get(v___x_360_, 4);
v_env_362_ = lean_ctor_get(v___x_360_, 0);
v_nextMacroScope_363_ = lean_ctor_get(v___x_360_, 1);
v_ngen_364_ = lean_ctor_get(v___x_360_, 2);
v_auxDeclNGen_365_ = lean_ctor_get(v___x_360_, 3);
v_cache_366_ = lean_ctor_get(v___x_360_, 5);
v_messages_367_ = lean_ctor_get(v___x_360_, 6);
v_infoState_368_ = lean_ctor_get(v___x_360_, 7);
v_snapshotTasks_369_ = lean_ctor_get(v___x_360_, 8);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_388_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_388_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snapshotTasks_369_);
lean_inc(v_infoState_368_);
lean_inc(v_messages_367_);
lean_inc(v_cache_366_);
lean_inc(v_traceState_361_);
lean_inc(v_auxDeclNGen_365_);
lean_inc(v_ngen_364_);
lean_inc(v_nextMacroScope_363_);
lean_inc(v_env_362_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_388_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint64_t v_tid_373_; lean_object* v_traces_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_387_; 
v_tid_373_ = lean_ctor_get_uint64(v_traceState_361_, sizeof(void*)*1);
v_traces_374_ = lean_ctor_get(v_traceState_361_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_traceState_361_);
if (v_isSharedCheck_387_ == 0)
{
v___x_376_ = v_traceState_361_;
v_isShared_377_ = v_isSharedCheck_387_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_traces_374_);
lean_dec(v_traceState_361_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_387_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_316_, v_traces_374_);
lean_dec_ref(v_traces_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_378_);
lean_ctor_set_uint64(v_reuseFailAlloc_386_, sizeof(void*)*1, v_tid_373_);
v___x_380_ = v_reuseFailAlloc_386_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_380_);
v___x_382_ = v___x_371_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_env_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_nextMacroScope_363_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_ngen_364_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_auxDeclNGen_365_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_385_, 5, v_cache_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 6, v_messages_367_);
lean_ctor_set(v_reuseFailAlloc_385_, 7, v_infoState_368_);
lean_ctor_set(v_reuseFailAlloc_385_, 8, v_snapshotTasks_369_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_st_ref_set(v___y_320_, v___x_382_);
v___x_384_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(v_fst_322_);
return v___x_384_;
}
}
}
}
}
else
{
goto v___jp_353_;
}
}
else
{
goto v___jp_353_;
}
}
v___jp_389_:
{
double v___x_391_; double v___x_392_; double v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_unbox_float(v_snd_339_);
v___x_392_ = lean_unbox_float(v_fst_338_);
v___x_393_ = lean_float_sub(v___x_391_, v___x_392_);
v___x_394_ = lean_float_decLt(v___y_390_, v___x_393_);
v___y_359_ = v___x_394_;
goto v___jp_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v_cls_405_, lean_object* v_collapsed_406_, lean_object* v_tag_407_, lean_object* v_opts_408_, lean_object* v_clsEnabled_409_, lean_object* v_oldTraces_410_, lean_object* v_msg_411_, lean_object* v_resStartStop_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v_collapsed_boxed_416_; uint8_t v_clsEnabled_boxed_417_; lean_object* v_res_418_; 
v_collapsed_boxed_416_ = lean_unbox(v_collapsed_406_);
v_clsEnabled_boxed_417_ = lean_unbox(v_clsEnabled_409_);
v_res_418_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2(v_cls_405_, v_collapsed_boxed_416_, v_tag_407_, v_opts_408_, v_clsEnabled_boxed_417_, v_oldTraces_410_, v_msg_411_, v_resStartStop_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec_ref(v_opts_408_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_name_419_, lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_426_ == 0)
{
lean_object* v___x_6532__overap_427_; lean_object* v___x_428_; 
v___x_6532__overap_427_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
lean_inc(v___x_6532__overap_427_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v_name_419_);
v___x_428_ = lean_apply_4(v___x_6532__overap_427_, v_name_419_, v___y_423_, v___y_424_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_440_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_440_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_440_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_440_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_a_429_);
if (v___x_433_ == 0)
{
size_t v___x_434_; size_t v___x_435_; 
lean_del_object(v___x_431_);
lean_dec(v_a_429_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_421_, v___x_434_);
v_i_421_ = v___x_435_;
goto _start;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_name_419_);
if (v_isShared_432_ == 0)
{
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_429_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_dec(v_name_419_);
return v___x_428_;
}
}
else
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_name_419_);
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_name_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
size_t v_i_boxed_451_; size_t v_stop_boxed_452_; lean_object* v_res_453_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_452_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(v_name_444_, v_as_445_, v_i_boxed_451_, v_stop_boxed_452_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v_as_445_);
return v_res_453_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__3(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1000000000u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_464_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__5));
v___x_465_ = l_Lean_Name_append(v___x_464_, v___x_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_options_470_; lean_object* v_inheritedTraceOptions_471_; uint8_t v_hasTrace_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___y_476_; uint8_t v___x_493_; 
v_options_470_ = lean_ctor_get(v_a_467_, 2);
v_inheritedTraceOptions_471_ = lean_ctor_get(v_a_467_, 13);
v_hasTrace_472_ = lean_ctor_get_uint8(v_options_470_, sizeof(void*)*1);
v___x_473_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_474_ = lean_box(0);
v___x_493_ = lean_bool_not(v_hasTrace_472_);
if (v___x_493_ == 0)
{
lean_object* v___f_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v_a_502_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; uint8_t v_a_518_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v_a_525_; lean_object* v___y_535_; uint8_t v___y_536_; lean_object* v___y_537_; uint8_t v_a_538_; uint8_t v___y_542_; uint8_t v_a_584_; 
lean_inc(v_name_466_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_494_, 0, v_name_466_);
v___x_495_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_496_ = 1;
v___x_497_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v_hasTrace_472_ == 0)
{
v_a_584_ = v_hasTrace_472_;
goto v___jp_583_;
}
else
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_471_, v_options_470_, v___x_596_);
if (v___x_597_ == 0)
{
v_a_584_ = v___x_597_;
goto v___jp_583_;
}
else
{
v___y_542_ = v___x_597_;
goto v___jp_541_;
}
}
v___jp_498_:
{
lean_object* v___x_503_; double v___x_504_; double v___x_505_; double v___x_506_; double v___x_507_; double v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_503_ = lean_io_mono_nanos_now();
v___x_504_ = lean_float_of_nat(v___y_499_);
v___x_505_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__3, &l_Lean_executeReservedNameAction___closed__3_once, _init_l_Lean_executeReservedNameAction___closed__3);
v___x_506_ = lean_float_div(v___x_504_, v___x_505_);
v___x_507_ = lean_float_of_nat(v___x_503_);
v___x_508_ = lean_float_div(v___x_507_, v___x_505_);
v___x_509_ = lean_box_float(v___x_506_);
v___x_510_ = lean_box_float(v___x_508_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_a_502_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2(v___x_495_, v___x_496_, v___x_497_, v_options_470_, v___y_500_, v___y_501_, v___f_494_, v___x_512_, v_a_467_, v_a_468_);
v___y_476_ = v___x_513_;
goto v___jp_475_;
}
v___jp_514_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(v_a_518_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___y_499_ = v___y_515_;
v___y_500_ = v___y_516_;
v___y_501_ = v___y_517_;
v_a_502_ = v___x_520_;
goto v___jp_498_;
}
v___jp_521_:
{
lean_object* v___x_526_; double v___x_527_; double v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_526_ = lean_io_get_num_heartbeats();
v___x_527_ = lean_float_of_nat(v___y_522_);
v___x_528_ = lean_float_of_nat(v___x_526_);
v___x_529_ = lean_box_float(v___x_527_);
v___x_530_ = lean_box_float(v___x_528_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_525_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2(v___x_495_, v___x_496_, v___x_497_, v_options_470_, v___y_523_, v___y_524_, v___f_494_, v___x_532_, v_a_467_, v_a_468_);
v___y_476_ = v___x_533_;
goto v___jp_475_;
}
v___jp_534_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(v_a_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___y_522_ = v___y_535_;
v___y_523_ = v___y_536_;
v___y_524_ = v___y_537_;
v_a_525_ = v___x_540_;
goto v___jp_521_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v_a_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_543_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__0___redArg(v_a_468_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = l_Lean_trace_profiler_useHeartbeats;
v___x_546_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_options_470_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_547_ = lean_io_mono_nanos_now();
v___x_548_ = lean_st_ref_get(v___x_473_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_array_get_size(v___x_548_);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v___x_548_);
lean_dec(v_name_466_);
v___y_515_ = v___x_547_;
v___y_516_ = v___y_542_;
v___y_517_ = v_a_544_;
v_a_518_ = v___x_546_;
goto v___jp_514_;
}
else
{
if (v___x_551_ == 0)
{
lean_dec(v___x_548_);
lean_dec(v_name_466_);
v___y_515_ = v___x_547_;
v___y_516_ = v___y_542_;
v___y_517_ = v_a_544_;
v_a_518_ = v___x_546_;
goto v___jp_514_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_550_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(v_name_466_, v___x_548_, v___x_552_, v___x_553_, v_a_467_, v_a_468_);
lean_dec(v___x_548_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; uint8_t v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
v___y_515_ = v___x_547_;
v___y_516_ = v___y_542_;
v___y_517_ = v_a_544_;
v_a_518_ = v___x_556_;
goto v___jp_514_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_a_557_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_554_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_499_ = v___x_547_;
v___y_500_ = v___y_542_;
v___y_501_ = v_a_544_;
v_a_502_ = v___x_562_;
goto v___jp_498_;
}
}
}
}
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_565_ = lean_io_get_num_heartbeats();
v___x_566_ = lean_st_ref_get(v___x_473_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v___x_566_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v___x_566_);
lean_dec(v_name_466_);
v___y_535_ = v___x_565_;
v___y_536_ = v___y_542_;
v___y_537_ = v_a_544_;
v_a_538_ = v___x_493_;
goto v___jp_534_;
}
else
{
if (v___x_569_ == 0)
{
lean_dec(v___x_566_);
lean_dec(v_name_466_);
v___y_535_ = v___x_565_;
v___y_536_ = v___y_542_;
v___y_537_ = v_a_544_;
v_a_538_ = v___x_493_;
goto v___jp_534_;
}
else
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_568_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(v_name_466_, v___x_566_, v___x_570_, v___x_571_, v_a_467_, v_a_468_);
lean_dec(v___x_566_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_unbox(v_a_573_);
lean_dec(v_a_573_);
v___y_535_ = v___x_565_;
v___y_536_ = v___y_542_;
v___y_537_ = v_a_544_;
v_a_538_ = v___x_574_;
goto v___jp_534_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_a_575_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_572_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v___y_522_ = v___x_565_;
v___y_523_ = v___y_542_;
v___y_524_ = v_a_544_;
v_a_525_ = v___x_580_;
goto v___jp_521_;
}
}
}
}
}
}
}
v___jp_583_:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = l_Lean_trace_profiler;
v___x_586_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_options_470_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
lean_dec_ref(v___f_494_);
v___x_587_ = lean_st_ref_get(v___x_473_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_array_get_size(v___x_587_);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v___x_587_);
lean_dec(v_name_466_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_474_);
return v___x_591_;
}
else
{
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v___x_587_);
lean_dec(v_name_466_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_474_);
return v___x_592_;
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_589_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(v_name_466_, v___x_587_, v___x_593_, v___x_594_, v_a_467_, v_a_468_);
lean_dec(v___x_587_);
v___y_476_ = v___x_595_;
goto v___jp_475_;
}
}
}
else
{
v___y_542_ = v_a_584_;
goto v___jp_541_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_598_ = lean_st_ref_get(v___x_473_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v___x_598_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v___x_598_);
lean_dec(v_name_466_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_474_);
return v___x_602_;
}
else
{
if (v___x_601_ == 0)
{
lean_object* v___x_603_; 
lean_dec(v___x_598_);
lean_dec(v_name_466_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_474_);
return v___x_603_;
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_600_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__3(v_name_466_, v___x_598_, v___x_604_, v___x_605_, v_a_467_, v_a_468_);
lean_dec(v___x_598_);
v___y_476_ = v___x_606_;
goto v___jp_475_;
}
}
}
v___jp_475_:
{
if (lean_obj_tag(v___y_476_) == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___y_476_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___y_476_, 0);
lean_dec(v_unused_484_);
v___x_478_ = v___y_476_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_dec(v___y_476_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_474_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_474_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___y_476_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___y_476_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___y_476_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___y_476_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_executeReservedNameAction(v_name_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3(lean_object* v_00_u03b1_612_, lean_object* v_x_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___redArg(v_x_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3___boxed(lean_object* v_00_u03b1_618_, lean_object* v_x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__3(v_00_u03b1_618_, v_x_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_623_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_631_, uint8_t v_suppressElabErrors_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 1)
{
lean_object* v_pre_634_; 
v_pre_634_ = lean_ctor_get(v_x_633_, 0);
switch(lean_obj_tag(v_pre_634_))
{
case 1:
{
lean_object* v_pre_635_; 
v_pre_635_ = lean_ctor_get(v_pre_634_, 0);
switch(lean_obj_tag(v_pre_635_))
{
case 0:
{
lean_object* v_str_636_; lean_object* v_str_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_str_636_ = lean_ctor_get(v_x_633_, 1);
v_str_637_ = lean_ctor_get(v_pre_634_, 1);
v___x_638_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_639_ = lean_string_dec_eq(v_str_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_641_ = lean_string_dec_eq(v_str_637_, v___x_640_);
if (v___x_641_ == 0)
{
return v___y_631_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_643_ = lean_string_dec_eq(v_str_636_, v___x_642_);
if (v___x_643_ == 0)
{
return v___y_631_;
}
else
{
return v_suppressElabErrors_632_;
}
}
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_645_ = lean_string_dec_eq(v_str_636_, v___x_644_);
if (v___x_645_ == 0)
{
return v___y_631_;
}
else
{
return v_suppressElabErrors_632_;
}
}
}
case 1:
{
lean_object* v_pre_646_; 
v_pre_646_ = lean_ctor_get(v_pre_635_, 0);
if (lean_obj_tag(v_pre_646_) == 0)
{
lean_object* v_str_647_; lean_object* v_str_648_; lean_object* v_str_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_str_647_ = lean_ctor_get(v_x_633_, 1);
v_str_648_ = lean_ctor_get(v_pre_634_, 1);
v_str_649_ = lean_ctor_get(v_pre_635_, 1);
v___x_650_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_651_ = lean_string_dec_eq(v_str_649_, v___x_650_);
if (v___x_651_ == 0)
{
return v___y_631_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_653_ = lean_string_dec_eq(v_str_648_, v___x_652_);
if (v___x_653_ == 0)
{
return v___y_631_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_655_ = lean_string_dec_eq(v_str_647_, v___x_654_);
if (v___x_655_ == 0)
{
return v___y_631_;
}
else
{
return v_suppressElabErrors_632_;
}
}
}
}
else
{
return v___y_631_;
}
}
default: 
{
return v___y_631_;
}
}
}
case 0:
{
lean_object* v_str_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_str_656_ = lean_ctor_get(v_x_633_, 1);
v___x_657_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_658_ = lean_string_dec_eq(v_str_656_, v___x_657_);
if (v___x_658_ == 0)
{
return v___y_631_;
}
else
{
return v_suppressElabErrors_632_;
}
}
default: 
{
return v___y_631_;
}
}
}
else
{
return v___y_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_659_, lean_object* v_suppressElabErrors_660_, lean_object* v_x_661_){
_start:
{
uint8_t v___y_4708__boxed_662_; uint8_t v_suppressElabErrors_boxed_663_; uint8_t v_res_664_; lean_object* v_r_665_; 
v___y_4708__boxed_662_ = lean_unbox(v___y_659_);
v_suppressElabErrors_boxed_663_ = lean_unbox(v_suppressElabErrors_660_);
v_res_664_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4708__boxed_662_, v_suppressElabErrors_boxed_663_, v_x_661_);
lean_dec(v_x_661_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_666_, lean_object* v_msgData_667_, uint8_t v_severity_668_, uint8_t v_isSilent_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; uint8_t v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; uint8_t v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; lean_object* v___y_746_; uint8_t v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; uint8_t v___y_751_; uint8_t v___y_752_; uint8_t v___x_757_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; uint8_t v___y_763_; uint8_t v___y_764_; uint8_t v___y_765_; uint8_t v___y_767_; uint8_t v___x_782_; 
v___x_757_ = 2;
v___x_782_ = l_Lean_instBEqMessageSeverity_beq(v_severity_668_, v___x_757_);
if (v___x_782_ == 0)
{
v___y_767_ = v___x_782_;
goto v___jp_766_;
}
else
{
uint8_t v___x_783_; 
lean_inc_ref(v_msgData_667_);
v___x_783_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_667_);
v___y_767_ = v___x_783_;
goto v___jp_766_;
}
v___jp_673_:
{
lean_object* v___x_683_; lean_object* v_currNamespace_684_; lean_object* v_openDecls_685_; lean_object* v_env_686_; lean_object* v_nextMacroScope_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_traceState_690_; lean_object* v_cache_691_; lean_object* v_messages_692_; lean_object* v_infoState_693_; lean_object* v_snapshotTasks_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_708_; 
v___x_683_ = lean_st_ref_take(v___y_682_);
v_currNamespace_684_ = lean_ctor_get(v___y_681_, 6);
v_openDecls_685_ = lean_ctor_get(v___y_681_, 7);
v_env_686_ = lean_ctor_get(v___x_683_, 0);
v_nextMacroScope_687_ = lean_ctor_get(v___x_683_, 1);
v_ngen_688_ = lean_ctor_get(v___x_683_, 2);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_683_, 3);
v_traceState_690_ = lean_ctor_get(v___x_683_, 4);
v_cache_691_ = lean_ctor_get(v___x_683_, 5);
v_messages_692_ = lean_ctor_get(v___x_683_, 6);
v_infoState_693_ = lean_ctor_get(v___x_683_, 7);
v_snapshotTasks_694_ = lean_ctor_get(v___x_683_, 8);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_708_ == 0)
{
v___x_696_ = v___x_683_;
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snapshotTasks_694_);
lean_inc(v_infoState_693_);
lean_inc(v_messages_692_);
lean_inc(v_cache_691_);
lean_inc(v_traceState_690_);
lean_inc(v_auxDeclNGen_689_);
lean_inc(v_ngen_688_);
lean_inc(v_nextMacroScope_687_);
lean_inc(v_env_686_);
lean_dec(v___x_683_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_openDecls_685_);
lean_inc(v_currNamespace_684_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_currNamespace_684_);
lean_ctor_set(v___x_698_, 1, v_openDecls_685_);
v___x_699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_675_);
lean_inc_ref(v___y_680_);
lean_inc_ref(v___y_676_);
v___x_700_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_700_, 0, v___y_676_);
lean_ctor_set(v___x_700_, 1, v___y_677_);
lean_ctor_set(v___x_700_, 2, v___y_679_);
lean_ctor_set(v___x_700_, 3, v___y_680_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5, v___y_674_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 1, v___y_678_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 2, v_isSilent_669_);
v___x_701_ = l_Lean_MessageLog_add(v___x_700_, v_messages_692_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 6, v___x_701_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_env_686_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_nextMacroScope_687_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_ngen_688_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_auxDeclNGen_689_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_traceState_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_cache_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_infoState_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_snapshotTasks_694_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_st_ref_set(v___y_682_, v___x_703_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
}
v___jp_709_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v___x_718_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_667_);
v___x_719_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(v___x_718_, v___y_670_, v___y_671_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_733_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc_ref_n(v___y_713_, 2);
v___x_724_ = l_Lean_FileMap_toPosition(v___y_713_, v___y_712_);
lean_dec(v___y_712_);
v___x_725_ = l_Lean_FileMap_toPosition(v___y_713_, v___y_717_);
lean_dec(v___y_717_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_715_ == 0)
{
lean_del_object(v___x_722_);
lean_dec_ref(v___y_710_);
v___y_674_ = v___y_711_;
v___y_675_ = v_a_720_;
v___y_676_ = v___y_714_;
v___y_677_ = v___x_724_;
v___y_678_ = v___y_716_;
v___y_679_ = v___x_726_;
v___y_680_ = v___x_727_;
v___y_681_ = v___y_670_;
v___y_682_ = v___y_671_;
goto v___jp_673_;
}
else
{
uint8_t v___x_728_; 
lean_inc(v_a_720_);
v___x_728_ = l_Lean_MessageData_hasTag(v___y_710_, v_a_720_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec_ref_known(v___x_726_, 1);
lean_dec_ref(v___x_724_);
lean_dec(v_a_720_);
v___x_729_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_729_);
v___x_731_ = v___x_722_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_del_object(v___x_722_);
v___y_674_ = v___y_711_;
v___y_675_ = v_a_720_;
v___y_676_ = v___y_714_;
v___y_677_ = v___x_724_;
v___y_678_ = v___y_716_;
v___y_679_ = v___x_726_;
v___y_680_ = v___x_727_;
v___y_681_ = v___y_670_;
v___y_682_ = v___y_671_;
goto v___jp_673_;
}
}
}
}
v___jp_734_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Syntax_getTailPos_x3f(v___y_736_, v___y_737_);
lean_dec(v___y_736_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_inc(v___y_742_);
v___y_710_ = v___y_735_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_742_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_739_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_740_;
v___y_717_ = v___y_742_;
goto v___jp_709_;
}
else
{
lean_object* v_val_744_; 
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
v___y_710_ = v___y_735_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_742_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_739_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_740_;
v___y_717_ = v_val_744_;
goto v___jp_709_;
}
}
v___jp_745_:
{
lean_object* v_ref_753_; lean_object* v___x_754_; 
v_ref_753_ = l_Lean_replaceRef(v_ref_666_, v___y_748_);
v___x_754_ = l_Lean_Syntax_getPos_x3f(v_ref_753_, v___y_747_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___y_735_ = v___y_746_;
v___y_736_ = v_ref_753_;
v___y_737_ = v___y_747_;
v___y_738_ = v___y_749_;
v___y_739_ = v___y_750_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_751_;
v___y_742_ = v___x_755_;
goto v___jp_734_;
}
else
{
lean_object* v_val_756_; 
v_val_756_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v___x_754_, 1);
v___y_735_ = v___y_746_;
v___y_736_ = v_ref_753_;
v___y_737_ = v___y_747_;
v___y_738_ = v___y_749_;
v___y_739_ = v___y_750_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_751_;
v___y_742_ = v_val_756_;
goto v___jp_734_;
}
}
v___jp_758_:
{
if (v___y_765_ == 0)
{
v___y_746_ = v___y_759_;
v___y_747_ = v___y_764_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_762_;
v___y_751_ = v___y_763_;
v___y_752_ = v_severity_668_;
goto v___jp_745_;
}
else
{
v___y_746_ = v___y_759_;
v___y_747_ = v___y_764_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_762_;
v___y_751_ = v___y_763_;
v___y_752_ = v___x_757_;
goto v___jp_745_;
}
}
v___jp_766_:
{
if (v___y_767_ == 0)
{
lean_object* v_fileName_768_; lean_object* v_fileMap_769_; lean_object* v_options_770_; lean_object* v_ref_771_; uint8_t v_suppressElabErrors_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___f_775_; uint8_t v___x_776_; uint8_t v___x_777_; 
v_fileName_768_ = lean_ctor_get(v___y_670_, 0);
v_fileMap_769_ = lean_ctor_get(v___y_670_, 1);
v_options_770_ = lean_ctor_get(v___y_670_, 2);
v_ref_771_ = lean_ctor_get(v___y_670_, 5);
v_suppressElabErrors_772_ = lean_ctor_get_uint8(v___y_670_, sizeof(void*)*14 + 1);
v___x_773_ = lean_box(v___y_767_);
v___x_774_ = lean_box(v_suppressElabErrors_772_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_775_, 0, v___x_773_);
lean_closure_set(v___f_775_, 1, v___x_774_);
v___x_776_ = 1;
v___x_777_ = l_Lean_instBEqMessageSeverity_beq(v_severity_668_, v___x_776_);
if (v___x_777_ == 0)
{
v___y_759_ = v___f_775_;
v___y_760_ = v_ref_771_;
v___y_761_ = v_fileMap_769_;
v___y_762_ = v_fileName_768_;
v___y_763_ = v_suppressElabErrors_772_;
v___y_764_ = v___y_767_;
v___y_765_ = v___x_777_;
goto v___jp_758_;
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = l_Lean_warningAsError;
v___x_779_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_options_770_, v___x_778_);
v___y_759_ = v___f_775_;
v___y_760_ = v_ref_771_;
v___y_761_ = v_fileMap_769_;
v___y_762_ = v_fileName_768_;
v___y_763_ = v_suppressElabErrors_772_;
v___y_764_ = v___y_767_;
v___y_765_ = v___x_779_;
goto v___jp_758_;
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_msgData_667_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_784_, lean_object* v_msgData_785_, lean_object* v_severity_786_, lean_object* v_isSilent_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_severity_boxed_791_; uint8_t v_isSilent_boxed_792_; lean_object* v_res_793_; 
v_severity_boxed_791_ = lean_unbox(v_severity_786_);
v_isSilent_boxed_792_ = lean_unbox(v_isSilent_787_);
v_res_793_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_784_, v_msgData_785_, v_severity_boxed_791_, v_isSilent_boxed_792_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v_ref_784_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_794_, uint8_t v_severity_795_, uint8_t v_isSilent_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_ref_800_; lean_object* v___x_801_; 
v_ref_800_ = lean_ctor_get(v___y_797_, 5);
v___x_801_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_800_, v_msgData_794_, v_severity_795_, v_isSilent_796_, v___y_797_, v___y_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_802_, lean_object* v_severity_803_, lean_object* v_isSilent_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_severity_boxed_808_; uint8_t v_isSilent_boxed_809_; lean_object* v_res_810_; 
v_severity_boxed_808_ = lean_unbox(v_severity_803_);
v_isSilent_boxed_809_ = lean_unbox(v_isSilent_804_);
v_res_810_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_802_, v_severity_boxed_808_, v_isSilent_boxed_809_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = 2;
v___x_816_ = 0;
v___x_817_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_811_, v___x_815_, v___x_816_, v___y_812_, v___y_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_822_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v___x_835_; 
lean_dec(v_id_829_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_x_831_);
return v___x_835_;
}
else
{
lean_object* v_head_836_; lean_object* v_tail_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_894_; 
v_head_836_ = lean_ctor_get(v_x_830_, 0);
v_tail_837_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_894_ == 0)
{
v___x_839_ = v_x_830_;
v_isShared_840_ = v_isSharedCheck_894_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_tail_837_);
lean_inc(v_head_836_);
lean_dec(v_x_830_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_894_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_fst_846_; lean_object* v___x_847_; lean_object* v_env_848_; uint8_t v___x_849_; uint8_t v___x_850_; 
v_fst_846_ = lean_ctor_get(v_head_836_, 0);
v___x_847_ = lean_st_ref_get(v___y_833_);
v_env_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_847_);
v___x_849_ = 1;
lean_inc(v_fst_846_);
v___x_850_ = l_Lean_Environment_contains(v_env_848_, v_fst_846_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_inc(v_fst_846_);
v___x_851_ = l_Lean_executeReservedNameAction(v_fst_846_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; lean_object* v_env_853_; uint8_t v___x_854_; 
lean_dec_ref_known(v___x_851_, 1);
v___x_852_ = lean_st_ref_get(v___y_833_);
v_env_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc_ref(v_env_853_);
lean_dec(v___x_852_);
v___x_854_ = l_Lean_Environment_containsOnBranch(v_env_853_, v_fst_846_);
lean_dec_ref(v_env_853_);
if (v___x_854_ == 0)
{
lean_del_object(v___x_839_);
lean_dec(v_head_836_);
v_x_830_ = v_tail_837_;
goto _start;
}
else
{
goto v___jp_841_;
}
}
else
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_839_);
v_isSharedCheck_891_ = !lean_is_exclusive(v_head_836_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_892_ = lean_ctor_get(v_head_836_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_head_836_, 0);
lean_dec(v_unused_893_);
v___x_857_ = v_head_836_;
v_isShared_858_ = v_isSharedCheck_891_;
goto v_resetjp_856_;
}
else
{
lean_dec(v_head_836_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_891_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_890_; 
v_a_859_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_890_ == 0)
{
v___x_861_ = v___x_851_;
v_isShared_862_ = v_isSharedCheck_890_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_851_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_890_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint8_t v___y_864_; uint8_t v___x_888_; 
v___x_888_ = l_Lean_Exception_isInterrupt(v_a_859_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; 
lean_inc(v_a_859_);
v___x_889_ = l_Lean_Exception_isRuntime(v_a_859_);
v___y_864_ = v___x_889_;
goto v___jp_863_;
}
else
{
v___y_864_ = v___x_888_;
goto v___jp_863_;
}
v___jp_863_:
{
if (v___y_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_del_object(v___x_861_);
v___x_865_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_829_);
v___x_866_ = l_Lean_MessageData_ofName(v_id_829_);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 7);
lean_ctor_set(v___x_857_, 1, v___x_866_);
lean_ctor_set(v___x_857_, 0, v___x_865_);
v___x_868_ = v___x_857_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_884_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_869_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_Exception_toMessageData(v_a_859_);
v___x_872_ = l_Lean_indentD(v___x_871_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_873_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref_known(v___x_874_, 1);
v_x_830_ = v_tail_837_;
goto _start;
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_tail_837_);
lean_dec(v_x_831_);
lean_dec(v_id_829_);
v_a_876_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_874_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
else
{
lean_object* v___x_886_; 
lean_del_object(v___x_857_);
lean_dec(v_tail_837_);
lean_dec(v_x_831_);
lean_dec(v_id_829_);
if (v_isShared_862_ == 0)
{
v___x_886_ = v___x_861_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_859_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
}
else
{
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_843_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_x_831_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_head_836_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_x_831_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v_x_830_ = v_tail_837_;
v_x_831_ = v___x_843_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_895_, v_x_896_, v_x_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_object* v___x_903_; 
v___x_903_ = lean_box(0);
return v___x_903_;
}
else
{
lean_object* v_head_904_; lean_object* v_tail_905_; lean_object* v_fst_906_; uint8_t v___x_907_; 
v_head_904_ = lean_ctor_get(v_x_902_, 0);
v_tail_905_ = lean_ctor_get(v_x_902_, 1);
v_fst_906_ = lean_ctor_get(v_head_904_, 0);
v___x_907_ = l_Lean_isPrivateName(v_fst_906_);
if (v___x_907_ == 0)
{
v_x_902_ = v_tail_905_;
goto _start;
}
else
{
lean_object* v___x_909_; 
lean_inc(v_head_904_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v_head_904_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_910_);
lean_dec(v_x_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
uint8_t v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 1;
v___x_917_ = 0;
v___x_918_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_912_, v___x_916_, v___x_917_, v___y_913_, v___y_914_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_options_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_options_927_ = lean_ctor_get(v___y_925_, 2);
v___x_928_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__1(v_options_927_, v_opt_924_);
v___x_929_ = lean_box(v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_931_, v___y_932_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_opt_931_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v_env_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_968_; 
v___x_945_ = lean_st_ref_get(v___y_943_);
v_env_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_946_);
lean_dec(v___x_945_);
v___x_947_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_948_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_947_, v___y_942_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_968_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_968_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_968_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v_isExporting_958_; 
v_isExporting_958_ = lean_ctor_get_uint8(v_env_946_, sizeof(void*)*8);
lean_dec_ref(v_env_946_);
if (v_isExporting_958_ == 0)
{
lean_dec(v_a_949_);
lean_dec(v_id_941_);
goto v___jp_953_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = l_Lean_isPrivateName(v_id_941_);
if (v___x_959_ == 0)
{
lean_dec(v_a_949_);
lean_dec(v_id_941_);
goto v___jp_953_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = lean_unbox(v_a_949_);
lean_dec(v_a_949_);
if (v___x_960_ == 0)
{
lean_dec(v_id_941_);
goto v___jp_953_;
}
else
{
lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_del_object(v___x_951_);
v___x_961_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_962_ = 0;
v___x_963_ = l_Lean_MessageData_ofConstName(v_id_941_, v___x_962_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_966_, v___y_942_, v___y_943_);
return v___x_967_;
}
}
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_974_, uint8_t v_enableLog_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v_env_980_; lean_object* v_options_981_; lean_object* v_currNamespace_982_; lean_object* v_openDecls_983_; lean_object* v___x_984_; lean_object* v_env_985_; lean_object* v_res_986_; 
v___x_979_ = lean_st_ref_get(v___y_977_);
v_env_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc_ref(v_env_980_);
lean_dec(v___x_979_);
v_options_981_ = lean_ctor_get(v___y_976_, 2);
v_currNamespace_982_ = lean_ctor_get(v___y_976_, 6);
v_openDecls_983_ = lean_ctor_get(v___y_976_, 7);
v___x_984_ = lean_st_ref_get(v___y_977_);
v_env_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_env_985_);
lean_dec(v___x_984_);
lean_inc(v_openDecls_983_);
lean_inc(v_currNamespace_982_);
v_res_986_ = l_Lean_ResolveName_resolveGlobalName(v_env_980_, v_options_981_, v_currNamespace_982_, v_openDecls_983_, v_id_974_);
if (v_enableLog_975_ == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v_env_985_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_res_986_);
return v___x_987_;
}
else
{
uint8_t v_isExporting_988_; 
v_isExporting_988_ = lean_ctor_get_uint8(v_env_985_, sizeof(void*)*8);
lean_dec_ref(v_env_985_);
if (v_isExporting_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_res_986_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_986_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v_fst_992_; lean_object* v___x_993_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v_fst_992_ = lean_ctor_get(v_val_991_, 0);
lean_inc(v_fst_992_);
lean_dec(v_val_991_);
v___x_993_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_992_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1001_);
v___x_995_ = v___x_993_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_993_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v_res_986_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_res_986_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_res_986_);
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v___x_1010_; 
lean_dec(v___x_990_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_res_986_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_1011_, lean_object* v_enableLog_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v_enableLog_boxed_1016_; lean_object* v_res_1017_; 
v_enableLog_boxed_1016_ = lean_unbox(v_enableLog_1012_);
v_res_1017_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1011_, v_enableLog_boxed_1016_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = 1;
lean_inc(v_id_1018_);
v___x_1023_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1018_, v___x_1022_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = lean_box(0);
v___x_1026_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1018_, v_a_1024_, v___x_1025_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = l_List_reverse___redArg(v_a_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
return v___x_1026_;
}
}
else
{
lean_dec(v_id_1018_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_realizeGlobalName(v_id_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1041_, v___y_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_opt_1046_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
if (lean_obj_tag(v_a_1051_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l_List_reverse___redArg(v_a_1052_);
return v___x_1053_;
}
else
{
lean_object* v_head_1054_; lean_object* v_tail_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_head_1054_ = lean_ctor_get(v_a_1051_, 0);
v_tail_1055_ = lean_ctor_get(v_a_1051_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_a_1051_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_tail_1055_);
lean_inc(v_head_1054_);
lean_dec(v_a_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_fst_1059_; lean_object* v___x_1061_; 
v_fst_1059_ = lean_ctor_get(v_head_1054_, 0);
lean_inc(v_fst_1059_);
lean_dec(v_head_1054_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_a_1052_);
lean_ctor_set(v___x_1057_, 0, v_fst_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_a_1052_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v_a_1051_ = v_tail_1055_;
v_a_1052_ = v___x_1061_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_ref_1069_; lean_object* v___x_1070_; lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v_ref_1069_ = lean_ctor_get(v___y_1066_, 5);
v___x_1070_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4(v_msg_1065_, v___y_1066_, v___y_1067_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
lean_inc(v_ref_1069_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_ref_1069_);
lean_ctor_set(v___x_1075_, 1, v_a_1071_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_fileName_1090_; lean_object* v_fileMap_1091_; lean_object* v_options_1092_; lean_object* v_currRecDepth_1093_; lean_object* v_maxRecDepth_1094_; lean_object* v_ref_1095_; lean_object* v_currNamespace_1096_; lean_object* v_openDecls_1097_; lean_object* v_initHeartbeats_1098_; lean_object* v_maxHeartbeats_1099_; lean_object* v_quotContext_1100_; lean_object* v_currMacroScope_1101_; uint8_t v_diag_1102_; lean_object* v_cancelTk_x3f_1103_; uint8_t v_suppressElabErrors_1104_; lean_object* v_inheritedTraceOptions_1105_; lean_object* v_ref_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_fileName_1090_ = lean_ctor_get(v___y_1087_, 0);
v_fileMap_1091_ = lean_ctor_get(v___y_1087_, 1);
v_options_1092_ = lean_ctor_get(v___y_1087_, 2);
v_currRecDepth_1093_ = lean_ctor_get(v___y_1087_, 3);
v_maxRecDepth_1094_ = lean_ctor_get(v___y_1087_, 4);
v_ref_1095_ = lean_ctor_get(v___y_1087_, 5);
v_currNamespace_1096_ = lean_ctor_get(v___y_1087_, 6);
v_openDecls_1097_ = lean_ctor_get(v___y_1087_, 7);
v_initHeartbeats_1098_ = lean_ctor_get(v___y_1087_, 8);
v_maxHeartbeats_1099_ = lean_ctor_get(v___y_1087_, 9);
v_quotContext_1100_ = lean_ctor_get(v___y_1087_, 10);
v_currMacroScope_1101_ = lean_ctor_get(v___y_1087_, 11);
v_diag_1102_ = lean_ctor_get_uint8(v___y_1087_, sizeof(void*)*14);
v_cancelTk_x3f_1103_ = lean_ctor_get(v___y_1087_, 12);
v_suppressElabErrors_1104_ = lean_ctor_get_uint8(v___y_1087_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1105_ = lean_ctor_get(v___y_1087_, 13);
v_ref_1106_ = l_Lean_replaceRef(v_ref_1085_, v_ref_1095_);
lean_inc_ref(v_inheritedTraceOptions_1105_);
lean_inc(v_cancelTk_x3f_1103_);
lean_inc(v_currMacroScope_1101_);
lean_inc(v_quotContext_1100_);
lean_inc(v_maxHeartbeats_1099_);
lean_inc(v_initHeartbeats_1098_);
lean_inc(v_openDecls_1097_);
lean_inc(v_currNamespace_1096_);
lean_inc(v_maxRecDepth_1094_);
lean_inc(v_currRecDepth_1093_);
lean_inc_ref(v_options_1092_);
lean_inc_ref(v_fileMap_1091_);
lean_inc_ref(v_fileName_1090_);
v___x_1107_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1107_, 0, v_fileName_1090_);
lean_ctor_set(v___x_1107_, 1, v_fileMap_1091_);
lean_ctor_set(v___x_1107_, 2, v_options_1092_);
lean_ctor_set(v___x_1107_, 3, v_currRecDepth_1093_);
lean_ctor_set(v___x_1107_, 4, v_maxRecDepth_1094_);
lean_ctor_set(v___x_1107_, 5, v_ref_1106_);
lean_ctor_set(v___x_1107_, 6, v_currNamespace_1096_);
lean_ctor_set(v___x_1107_, 7, v_openDecls_1097_);
lean_ctor_set(v___x_1107_, 8, v_initHeartbeats_1098_);
lean_ctor_set(v___x_1107_, 9, v_maxHeartbeats_1099_);
lean_ctor_set(v___x_1107_, 10, v_quotContext_1100_);
lean_ctor_set(v___x_1107_, 11, v_currMacroScope_1101_);
lean_ctor_set(v___x_1107_, 12, v_cancelTk_x3f_1103_);
lean_ctor_set(v___x_1107_, 13, v_inheritedTraceOptions_1105_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*14, v_diag_1102_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*14 + 1, v_suppressElabErrors_1104_);
v___x_1108_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1086_, v___x_1107_, v___y_1088_);
lean_dec_ref_known(v___x_1107_, 14);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1109_, lean_object* v_msg_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1109_, v_msg_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v_ref_1109_);
return v_res_1114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1136_, lean_object* v_declHint_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; uint8_t v___y_1143_; uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1140_ = lean_st_ref_get(v___y_1138_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1199_ = l_Lean_Name_isAnonymous(v_declHint_1137_);
v___x_1200_ = lean_bool_not(v___x_1199_);
if (v___x_1200_ == 0)
{
v___y_1143_ = v___x_1200_;
goto v___jp_1142_;
}
else
{
uint8_t v_isExporting_1201_; 
v_isExporting_1201_ = lean_ctor_get_uint8(v_env_1141_, sizeof(void*)*8);
v___y_1143_ = v_isExporting_1201_;
goto v___jp_1142_;
}
v___jp_1142_:
{
if (v___y_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_env_1141_);
lean_dec(v_declHint_1137_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_msg_1136_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = 0;
lean_inc_ref(v_env_1141_);
v___x_1146_ = l_Lean_Environment_setExporting(v_env_1141_, v___x_1145_);
lean_inc(v_declHint_1137_);
lean_inc_ref(v___x_1146_);
v___x_1147_ = l_Lean_Environment_contains(v___x_1146_, v_declHint_1137_, v___y_1143_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v___x_1146_);
lean_dec_ref(v_env_1141_);
lean_dec(v_declHint_1137_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1136_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_c_1154_; lean_object* v___x_1155_; 
v___x_1149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__2);
v___x_1150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__2_spec__2_spec__4___closed__5);
v___x_1151_ = l_Lean_Options_empty;
v___x_1152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1146_);
lean_ctor_set(v___x_1152_, 1, v___x_1149_);
lean_ctor_set(v___x_1152_, 2, v___x_1150_);
lean_ctor_set(v___x_1152_, 3, v___x_1151_);
lean_inc(v_declHint_1137_);
v___x_1153_ = l_Lean_MessageData_ofConstName(v_declHint_1137_, v___x_1145_);
v_c_1154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1154_, 0, v___x_1152_);
lean_ctor_set(v_c_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1141_, v_declHint_1137_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v_env_1141_);
lean_dec(v_declHint_1137_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_c_1154_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1136_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1198_; 
v_val_1163_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1165_ = v___x_1155_;
v_isShared_1166_ = v_isSharedCheck_1198_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_val_1163_);
lean_dec(v___x_1155_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1198_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_mod_1170_; uint8_t v___x_1171_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_Environment_header(v_env_1141_);
lean_dec_ref(v_env_1141_);
v___x_1169_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1168_);
v_mod_1170_ = lean_array_get(v___x_1167_, v___x_1169_, v_val_1163_);
lean_dec(v_val_1163_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_isPrivateName(v_declHint_1137_);
lean_dec(v_declHint_1137_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_c_1154_);
v___x_1174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_MessageData_ofName(v_mod_1170_);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Lean_MessageData_note(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_msg_1136_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1181_);
v___x_1183_ = v___x_1165_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_c_1154_);
v___x_1187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_MessageData_ofName(v_mod_1170_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_note(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_msg_1136_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1194_);
v___x_1196_ = v___x_1165_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1202_, lean_object* v_declHint_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1202_, v_declHint_1203_, v___y_1204_);
lean_dec(v___y_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1207_, lean_object* v_declHint_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1222_; 
v___x_1212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1207_, v_declHint_1208_, v___y_1210_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = l_Lean_unknownIdentifierMessageTag;
v___x_1218_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_a_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1223_, lean_object* v_declHint_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1223_, v_declHint_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1229_, lean_object* v_msg_1230_, lean_object* v_declHint_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_a_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1230_, v_declHint_1231_, v___y_1232_, v___y_1233_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1229_, v_a_1236_, v___y_1232_, v___y_1233_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1238_, lean_object* v_msg_1239_, lean_object* v_declHint_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1238_, v_msg_1239_, v_declHint_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_ref_1238_);
return v_res_1244_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1251_, lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1256_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1257_ = 0;
lean_inc(v_constName_1252_);
v___x_1258_ = l_Lean_MessageData_ofConstName(v_constName_1252_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1256_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1251_, v___x_1261_, v_constName_1252_, v___y_1253_, v___y_1254_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1263_, lean_object* v_constName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1263_, v_constName_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_ref_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
if (lean_obj_tag(v_a_1269_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = l_List_reverse___redArg(v_a_1270_);
return v___x_1271_;
}
else
{
lean_object* v_head_1272_; lean_object* v_tail_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1284_; 
v_head_1272_ = lean_ctor_get(v_a_1269_, 0);
v_tail_1273_ = lean_ctor_get(v_a_1269_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1269_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1275_ = v_a_1269_;
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_tail_1273_);
lean_inc(v_head_1272_);
lean_dec(v_a_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_snd_1277_; uint8_t v___x_1278_; 
v_snd_1277_ = lean_ctor_get(v_head_1272_, 1);
v___x_1278_ = l_List_isEmpty___redArg(v_snd_1277_);
if (v___x_1278_ == 0)
{
lean_del_object(v___x_1275_);
lean_dec(v_head_1272_);
v_a_1269_ = v_tail_1273_;
goto _start;
}
else
{
lean_object* v___x_1281_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v_a_1270_);
v___x_1281_ = v___x_1275_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_head_1272_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1270_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v_a_1269_ = v_tail_1273_;
v_a_1270_ = v___x_1281_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1285_, lean_object* v_cs_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_cs_1291_; uint8_t v___x_1295_; 
v___x_1290_ = lean_box(0);
v_cs_1291_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1286_, v___x_1290_);
v___x_1295_ = l_List_isEmpty___redArg(v_cs_1291_);
if (v___x_1295_ == 0)
{
lean_dec(v_n_1285_);
goto v___jp_1292_;
}
else
{
lean_object* v_ref_1296_; lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_cs_1291_);
v_ref_1296_ = lean_ctor_get(v___y_1287_, 5);
v___x_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1296_, v_n_1285_, v___y_1287_, v___y_1288_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1291_, v___x_1290_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1306_, lean_object* v_cs_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1306_, v_cs_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
lean_inc(v_n_1312_);
v___x_1316_ = l_Lean_realizeGlobalName(v_n_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1312_, v_a_1317_, v_a_1313_, v_a_1314_);
return v___x_1318_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_n_1312_);
v_a_1319_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1316_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_realizeGlobalConstCore(v_n_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1332_, lean_object* v_ref_1333_, lean_object* v_constName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1333_, v_constName_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_ref_1340_, lean_object* v_constName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1339_, v_ref_1340_, v_constName_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v_ref_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1346_, lean_object* v_ref_1347_, lean_object* v_msg_1348_, lean_object* v_declHint_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1347_, v_msg_1348_, v_declHint_1349_, v___y_1350_, v___y_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_ref_1355_, lean_object* v_msg_1356_, lean_object* v_declHint_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1354_, v_ref_1355_, v_msg_1356_, v_declHint_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_ref_1355_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1362_, lean_object* v_declHint_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1362_, v_declHint_1363_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1368_, lean_object* v_declHint_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1368_, v_declHint_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1374_, lean_object* v_ref_1375_, lean_object* v_msg_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1375_, v_msg_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_ref_1382_, lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1381_, v_ref_1382_, v_msg_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v_ref_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1389_, v___y_1390_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1394_, v_msg_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
if (lean_obj_tag(v_a_1400_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = l_List_reverse___redArg(v_a_1401_);
return v___x_1402_;
}
else
{
lean_object* v_head_1403_; lean_object* v_tail_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v_head_1403_ = lean_ctor_get(v_a_1400_, 0);
v_tail_1404_ = lean_ctor_get(v_a_1400_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1400_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1406_ = v_a_1400_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_tail_1404_);
lean_inc(v_head_1403_);
lean_dec(v_a_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = l_Lean_MessageData_ofExpr(v_head_1403_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_a_1401_);
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_a_1401_);
v___x_1410_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v_a_1400_ = v_tail_1404_;
v_a_1401_ = v___x_1410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
if (lean_obj_tag(v_a_1414_) == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = l_List_reverse___redArg(v_a_1415_);
return v___x_1416_;
}
else
{
lean_object* v_head_1417_; lean_object* v_tail_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1428_; 
v_head_1417_ = lean_ctor_get(v_a_1414_, 0);
v_tail_1418_ = lean_ctor_get(v_a_1414_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1414_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1420_ = v_a_1414_;
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_tail_1418_);
lean_inc(v_head_1417_);
lean_dec(v_a_1414_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Lean_mkConst(v_head_1417_, v___x_1422_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_a_1415_);
lean_ctor_set(v___x_1420_, 0, v___x_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_a_1415_);
v___x_1425_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v_a_1414_ = v_tail_1418_;
v_a_1415_ = v___x_1425_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1435_, lean_object* v_cs_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
if (lean_obj_tag(v_cs_1436_) == 1)
{
lean_object* v_tail_1452_; 
v_tail_1452_ = lean_ctor_get(v_cs_1436_, 1);
if (lean_obj_tag(v_tail_1452_) == 0)
{
lean_object* v_head_1453_; lean_object* v___x_1454_; 
lean_dec(v_n_1435_);
v_head_1453_ = lean_ctor_get(v_cs_1436_, 0);
lean_inc(v_head_1453_);
lean_dec_ref_known(v_cs_1436_, 2);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_head_1453_);
return v___x_1454_;
}
else
{
goto v___jp_1440_;
}
}
else
{
goto v___jp_1440_;
}
v___jp_1440_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1441_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1442_ = l_Lean_MessageData_ofName(v_n_1435_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_box(0);
v___x_1447_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1436_, v___x_1446_);
v___x_1448_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1447_, v___x_1446_);
v___x_1449_ = l_Lean_MessageData_ofList(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1445_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1450_, v___y_1437_, v___y_1438_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1455_, lean_object* v_cs_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1455_, v_cs_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
lean_inc(v_n_1461_);
v___x_1465_ = l_Lean_realizeGlobalConstCore(v_n_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1461_, v_a_1466_, v_a_1462_, v_a_1463_);
return v___x_1467_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_n_1461_);
v_a_1468_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1465_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1465_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
if (lean_obj_tag(v_a_1481_) == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_array_to_list(v_a_1482_);
return v___x_1483_;
}
else
{
lean_object* v_head_1484_; 
v_head_1484_ = lean_ctor_get(v_a_1481_, 0);
if (lean_obj_tag(v_head_1484_) == 1)
{
lean_object* v_fields_1485_; 
v_fields_1485_ = lean_ctor_get(v_head_1484_, 1);
if (lean_obj_tag(v_fields_1485_) == 0)
{
lean_object* v_tail_1486_; lean_object* v_n_1487_; lean_object* v___x_1488_; 
lean_inc_ref(v_head_1484_);
v_tail_1486_ = lean_ctor_get(v_a_1481_, 1);
lean_inc(v_tail_1486_);
lean_dec_ref_known(v_a_1481_, 2);
v_n_1487_ = lean_ctor_get(v_head_1484_, 0);
lean_inc(v_n_1487_);
lean_dec_ref_known(v_head_1484_, 2);
v___x_1488_ = lean_array_push(v_a_1482_, v_n_1487_);
v_a_1481_ = v_tail_1486_;
v_a_1482_ = v___x_1488_;
goto _start;
}
else
{
lean_object* v_tail_1490_; 
v_tail_1490_ = lean_ctor_get(v_a_1481_, 1);
lean_inc(v_tail_1490_);
lean_dec_ref_known(v_a_1481_, 2);
v_a_1481_ = v_tail_1490_;
goto _start;
}
}
else
{
lean_object* v_tail_1492_; 
v_tail_1492_ = lean_ctor_get(v_a_1481_, 1);
lean_inc(v_tail_1492_);
lean_dec_ref_known(v_a_1481_, 2);
v_a_1481_ = v_tail_1492_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1500_ = l_Lean_MessageData_ofFormat(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1501_, lean_object* v_k_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
if (lean_obj_tag(v_stx_1501_) == 3)
{
lean_object* v_val_1506_; lean_object* v_preresolved_1507_; lean_object* v___x_1508_; lean_object* v_pre_1509_; uint8_t v___x_1510_; 
v_val_1506_ = lean_ctor_get(v_stx_1501_, 2);
lean_inc(v_val_1506_);
v_preresolved_1507_ = lean_ctor_get(v_stx_1501_, 3);
v___x_1508_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1507_);
v_pre_1509_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1507_, v___x_1508_);
v___x_1510_ = l_List_isEmpty___redArg(v_pre_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec(v_val_1506_);
lean_dec_ref_known(v_stx_1501_, 4);
lean_dec_ref(v_k_1502_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_pre_1509_);
return v___x_1511_;
}
else
{
lean_object* v_fileName_1512_; lean_object* v_fileMap_1513_; lean_object* v_options_1514_; lean_object* v_currRecDepth_1515_; lean_object* v_maxRecDepth_1516_; lean_object* v_ref_1517_; lean_object* v_currNamespace_1518_; lean_object* v_openDecls_1519_; lean_object* v_initHeartbeats_1520_; lean_object* v_maxHeartbeats_1521_; lean_object* v_quotContext_1522_; lean_object* v_currMacroScope_1523_; uint8_t v_diag_1524_; lean_object* v_cancelTk_x3f_1525_; uint8_t v_suppressElabErrors_1526_; lean_object* v_inheritedTraceOptions_1527_; lean_object* v_ref_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_pre_1509_);
v_fileName_1512_ = lean_ctor_get(v___y_1503_, 0);
v_fileMap_1513_ = lean_ctor_get(v___y_1503_, 1);
v_options_1514_ = lean_ctor_get(v___y_1503_, 2);
v_currRecDepth_1515_ = lean_ctor_get(v___y_1503_, 3);
v_maxRecDepth_1516_ = lean_ctor_get(v___y_1503_, 4);
v_ref_1517_ = lean_ctor_get(v___y_1503_, 5);
v_currNamespace_1518_ = lean_ctor_get(v___y_1503_, 6);
v_openDecls_1519_ = lean_ctor_get(v___y_1503_, 7);
v_initHeartbeats_1520_ = lean_ctor_get(v___y_1503_, 8);
v_maxHeartbeats_1521_ = lean_ctor_get(v___y_1503_, 9);
v_quotContext_1522_ = lean_ctor_get(v___y_1503_, 10);
v_currMacroScope_1523_ = lean_ctor_get(v___y_1503_, 11);
v_diag_1524_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*14);
v_cancelTk_x3f_1525_ = lean_ctor_get(v___y_1503_, 12);
v_suppressElabErrors_1526_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1527_ = lean_ctor_get(v___y_1503_, 13);
v_ref_1528_ = l_Lean_replaceRef(v_stx_1501_, v_ref_1517_);
lean_dec_ref_known(v_stx_1501_, 4);
lean_inc_ref(v_inheritedTraceOptions_1527_);
lean_inc(v_cancelTk_x3f_1525_);
lean_inc(v_currMacroScope_1523_);
lean_inc(v_quotContext_1522_);
lean_inc(v_maxHeartbeats_1521_);
lean_inc(v_initHeartbeats_1520_);
lean_inc(v_openDecls_1519_);
lean_inc(v_currNamespace_1518_);
lean_inc(v_maxRecDepth_1516_);
lean_inc(v_currRecDepth_1515_);
lean_inc_ref(v_options_1514_);
lean_inc_ref(v_fileMap_1513_);
lean_inc_ref(v_fileName_1512_);
v___x_1529_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1529_, 0, v_fileName_1512_);
lean_ctor_set(v___x_1529_, 1, v_fileMap_1513_);
lean_ctor_set(v___x_1529_, 2, v_options_1514_);
lean_ctor_set(v___x_1529_, 3, v_currRecDepth_1515_);
lean_ctor_set(v___x_1529_, 4, v_maxRecDepth_1516_);
lean_ctor_set(v___x_1529_, 5, v_ref_1528_);
lean_ctor_set(v___x_1529_, 6, v_currNamespace_1518_);
lean_ctor_set(v___x_1529_, 7, v_openDecls_1519_);
lean_ctor_set(v___x_1529_, 8, v_initHeartbeats_1520_);
lean_ctor_set(v___x_1529_, 9, v_maxHeartbeats_1521_);
lean_ctor_set(v___x_1529_, 10, v_quotContext_1522_);
lean_ctor_set(v___x_1529_, 11, v_currMacroScope_1523_);
lean_ctor_set(v___x_1529_, 12, v_cancelTk_x3f_1525_);
lean_ctor_set(v___x_1529_, 13, v_inheritedTraceOptions_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*14, v_diag_1524_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*14 + 1, v_suppressElabErrors_1526_);
lean_inc(v___y_1504_);
v___x_1530_ = lean_apply_4(v_k_1502_, v_val_1506_, v___x_1529_, v___y_1504_, lean_box(0));
return v___x_1530_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec_ref(v_k_1502_);
v___x_1531_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1532_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1501_, v___x_1531_, v___y_1503_, v___y_1504_);
lean_dec(v_stx_1501_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1533_, lean_object* v_k_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1533_, v_k_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_fileName_1544_; lean_object* v_fileMap_1545_; lean_object* v_options_1546_; lean_object* v_currRecDepth_1547_; lean_object* v_maxRecDepth_1548_; lean_object* v_ref_1549_; lean_object* v_currNamespace_1550_; lean_object* v_openDecls_1551_; lean_object* v_initHeartbeats_1552_; lean_object* v_maxHeartbeats_1553_; lean_object* v_quotContext_1554_; lean_object* v_currMacroScope_1555_; uint8_t v_diag_1556_; lean_object* v_cancelTk_x3f_1557_; uint8_t v_suppressElabErrors_1558_; lean_object* v_inheritedTraceOptions_1559_; lean_object* v___x_1560_; lean_object* v_ref_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_fileName_1544_ = lean_ctor_get(v_a_1541_, 0);
v_fileMap_1545_ = lean_ctor_get(v_a_1541_, 1);
v_options_1546_ = lean_ctor_get(v_a_1541_, 2);
v_currRecDepth_1547_ = lean_ctor_get(v_a_1541_, 3);
v_maxRecDepth_1548_ = lean_ctor_get(v_a_1541_, 4);
v_ref_1549_ = lean_ctor_get(v_a_1541_, 5);
v_currNamespace_1550_ = lean_ctor_get(v_a_1541_, 6);
v_openDecls_1551_ = lean_ctor_get(v_a_1541_, 7);
v_initHeartbeats_1552_ = lean_ctor_get(v_a_1541_, 8);
v_maxHeartbeats_1553_ = lean_ctor_get(v_a_1541_, 9);
v_quotContext_1554_ = lean_ctor_get(v_a_1541_, 10);
v_currMacroScope_1555_ = lean_ctor_get(v_a_1541_, 11);
v_diag_1556_ = lean_ctor_get_uint8(v_a_1541_, sizeof(void*)*14);
v_cancelTk_x3f_1557_ = lean_ctor_get(v_a_1541_, 12);
v_suppressElabErrors_1558_ = lean_ctor_get_uint8(v_a_1541_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1559_ = lean_ctor_get(v_a_1541_, 13);
v___x_1560_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1561_ = l_Lean_replaceRef(v_stx_1540_, v_ref_1549_);
lean_inc_ref(v_inheritedTraceOptions_1559_);
lean_inc(v_cancelTk_x3f_1557_);
lean_inc(v_currMacroScope_1555_);
lean_inc(v_quotContext_1554_);
lean_inc(v_maxHeartbeats_1553_);
lean_inc(v_initHeartbeats_1552_);
lean_inc(v_openDecls_1551_);
lean_inc(v_currNamespace_1550_);
lean_inc(v_maxRecDepth_1548_);
lean_inc(v_currRecDepth_1547_);
lean_inc_ref(v_options_1546_);
lean_inc_ref(v_fileMap_1545_);
lean_inc_ref(v_fileName_1544_);
v___x_1562_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1562_, 0, v_fileName_1544_);
lean_ctor_set(v___x_1562_, 1, v_fileMap_1545_);
lean_ctor_set(v___x_1562_, 2, v_options_1546_);
lean_ctor_set(v___x_1562_, 3, v_currRecDepth_1547_);
lean_ctor_set(v___x_1562_, 4, v_maxRecDepth_1548_);
lean_ctor_set(v___x_1562_, 5, v_ref_1561_);
lean_ctor_set(v___x_1562_, 6, v_currNamespace_1550_);
lean_ctor_set(v___x_1562_, 7, v_openDecls_1551_);
lean_ctor_set(v___x_1562_, 8, v_initHeartbeats_1552_);
lean_ctor_set(v___x_1562_, 9, v_maxHeartbeats_1553_);
lean_ctor_set(v___x_1562_, 10, v_quotContext_1554_);
lean_ctor_set(v___x_1562_, 11, v_currMacroScope_1555_);
lean_ctor_set(v___x_1562_, 12, v_cancelTk_x3f_1557_);
lean_ctor_set(v___x_1562_, 13, v_inheritedTraceOptions_1559_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*14, v_diag_1556_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*14 + 1, v_suppressElabErrors_1558_);
v___x_1563_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1540_, v___x_1560_, v___x_1562_, v_a_1542_);
lean_dec_ref_known(v___x_1562_, 14);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_realizeGlobalConst(v_stx_1564_, v_a_1565_, v_a_1566_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1568_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_instMonadEIO(lean_box(0));
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_toApplicative_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1609_; 
v___x_1576_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1577_ = l_StateRefT_x27_instMonad___redArg(v___x_1576_);
v_toApplicative_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1577_, 1);
lean_dec(v_unused_1610_);
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1609_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_toApplicative_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1609_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_toFunctor_1582_; lean_object* v_toSeq_1583_; lean_object* v_toSeqLeft_1584_; lean_object* v_toSeqRight_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1607_; 
v_toFunctor_1582_ = lean_ctor_get(v_toApplicative_1578_, 0);
v_toSeq_1583_ = lean_ctor_get(v_toApplicative_1578_, 2);
v_toSeqLeft_1584_ = lean_ctor_get(v_toApplicative_1578_, 3);
v_toSeqRight_1585_ = lean_ctor_get(v_toApplicative_1578_, 4);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_toApplicative_1578_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_toApplicative_1578_, 1);
lean_dec(v_unused_1608_);
v___x_1587_ = v_toApplicative_1578_;
v_isShared_1588_ = v_isSharedCheck_1607_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_toSeqRight_1585_);
lean_inc(v_toSeqLeft_1584_);
lean_inc(v_toSeq_1583_);
lean_inc(v_toFunctor_1582_);
lean_dec(v_toApplicative_1578_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1607_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___f_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___x_1598_; 
v___f_1589_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1590_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1582_);
v___f_1591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1591_, 0, v_toFunctor_1582_);
v___f_1592_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1592_, 0, v_toFunctor_1582_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___f_1591_);
lean_ctor_set(v___x_1593_, 1, v___f_1592_);
v___f_1594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1594_, 0, v_toSeqRight_1585_);
v___f_1595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1595_, 0, v_toSeqLeft_1584_);
v___f_1596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1596_, 0, v_toSeq_1583_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 4, v___f_1594_);
lean_ctor_set(v___x_1587_, 3, v___f_1595_);
lean_ctor_set(v___x_1587_, 2, v___f_1596_);
lean_ctor_set(v___x_1587_, 1, v___f_1589_);
lean_ctor_set(v___x_1587_, 0, v___x_1593_);
v___x_1598_ = v___x_1587_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v___f_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v___f_1596_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___f_1595_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v___f_1594_);
v___x_1598_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v___f_1590_);
lean_ctor_set(v___x_1580_, 0, v___x_1598_);
v___x_1600_ = v___x_1580_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___f_1590_);
v___x_1600_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_195__overap_1603_; lean_object* v___x_1604_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = l_instInhabitedOfMonad___redArg(v___x_1600_, v___x_1601_);
v___x_195__overap_1603_ = lean_panic_fn_borrowed(v___x_1602_, v_msg_1572_);
lean_dec(v___x_1602_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
v___x_1604_ = lean_apply_3(v___x_195__overap_1603_, v___y_1573_, v___y_1574_, lean_box(0));
return v___x_1604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 0)
{
return v_x_1617_;
}
else
{
lean_object* v_head_1619_; lean_object* v_tail_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_head_1619_ = lean_ctor_get(v_x_1618_, 0);
v_tail_1620_ = lean_ctor_get(v_x_1618_, 1);
v___x_1621_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1622_ = lean_string_append(v_x_1617_, v___x_1621_);
v___x_1623_ = lean_expr_dbg_to_string(v_head_1619_);
v___x_1624_ = lean_string_append(v___x_1622_, v___x_1623_);
lean_dec_ref(v___x_1623_);
v_x_1617_ = v___x_1624_;
v_x_1618_ = v_tail_1620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1626_, v_x_1627_);
lean_dec(v_x_1627_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1633_;
}
else
{
lean_object* v_tail_1634_; 
v_tail_1634_ = lean_ctor_get(v_x_1632_, 1);
if (lean_obj_tag(v_tail_1634_) == 0)
{
lean_object* v_head_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_head_1635_ = lean_ctor_get(v_x_1632_, 0);
v___x_1636_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1637_ = lean_expr_dbg_to_string(v_head_1635_);
v___x_1638_ = lean_string_append(v___x_1636_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v_head_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint32_t v___x_1646_; lean_object* v___x_1647_; 
v_head_1641_ = lean_ctor_get(v_x_1632_, 0);
v___x_1642_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1643_ = lean_expr_dbg_to_string(v_head_1641_);
v___x_1644_ = lean_string_append(v___x_1642_, v___x_1643_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1644_, v_tail_1634_);
v___x_1646_ = 93;
v___x_1647_ = lean_string_push(v___x_1645_, v___x_1646_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1648_);
lean_dec(v_x_1648_);
return v_res_1649_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1654_ = lean_unsigned_to_nat(11u);
v___x_1655_ = lean_unsigned_to_nat(429u);
v___x_1656_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1657_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1658_ = l_mkPanicMessageWithDecl(v___x_1657_, v___x_1656_, v___x_1655_, v___x_1654_, v___x_1653_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1661_, lean_object* v_cs_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
if (lean_obj_tag(v_cs_1662_) == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_id_1661_);
v___x_1666_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1667_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1666_, v___y_1663_, v___y_1664_);
return v___x_1667_;
}
else
{
lean_object* v_tail_1668_; 
v_tail_1668_ = lean_ctor_get(v_cs_1662_, 1);
if (lean_obj_tag(v_tail_1668_) == 0)
{
lean_object* v_head_1669_; lean_object* v___x_1670_; 
lean_dec(v_id_1661_);
v_head_1669_ = lean_ctor_get(v_cs_1662_, 0);
lean_inc(v_head_1669_);
lean_dec_ref_known(v_cs_1662_, 2);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_head_1669_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1671_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1672_ = lean_box(0);
v___x_1673_ = 0;
lean_inc(v_id_1661_);
v___x_1674_ = l_Lean_Syntax_formatStx(v_id_1661_, v___x_1672_, v___x_1673_);
v___x_1675_ = l_Std_Format_defWidth;
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l_Std_Format_pretty(v___x_1674_, v___x_1675_, v___x_1676_, v___x_1676_);
v___x_1678_ = lean_string_append(v___x_1671_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
v___x_1681_ = lean_box(0);
v___x_1682_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1662_, v___x_1681_);
v___x_1683_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1682_);
lean_dec(v___x_1682_);
v___x_1684_ = lean_string_append(v___x_1680_, v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___x_1686_ = l_Lean_MessageData_ofFormat(v___x_1685_);
v___x_1687_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1661_, v___x_1686_, v___y_1663_, v___y_1664_);
lean_dec(v_id_1661_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1688_, lean_object* v_cs_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1688_, v_cs_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
lean_inc(v_id_1694_);
v___x_1698_ = l_Lean_realizeGlobalConst(v_id_1694_, v_a_1695_, v_a_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1694_, v_a_1699_, v_a_1695_, v_a_1696_);
return v___x_1700_;
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_id_1694_);
v_a_1701_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1698_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1698_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_realizeGlobalConstNoOverload(v_id_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1713_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_unsigned_to_nat(3863082579u);
v___x_1746_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1747_ = l_Lean_Name_num___override(v___x_1746_, v___x_1745_);
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1750_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1751_ = l_Lean_Name_str___override(v___x_1750_, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1754_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1755_ = l_Lean_Name_str___override(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_unsigned_to_nat(2u);
v___x_1757_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1758_ = l_Lean_Name_num___override(v___x_1757_, v___x_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1761_ = 0;
v___x_1762_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1763_ = l_Lean_registerTraceClass(v___x_1760_, v___x_1761_, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1765_;
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

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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
uint8_t l_Lean_initializing();
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21;
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
lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2____boxed(lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
return v_res_9_;
}
}
static lean_object* _init_l_Lean_registerReservedNameAction___closed__1(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_registerReservedNameAction___closed__0));
v___x_12_ = lean_mk_io_user_error(v___x_11_);
return v___x_12_;
}
}
lean_object* l_Lean_registerReservedNameAction(lean_object* v_act_13_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_Lean_initializing();
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec_ref(v_act_13_);
v___x_16_ = lean_obj_once(&l_Lean_registerReservedNameAction___closed__1, &l_Lean_registerReservedNameAction___closed__1_once, _init_l_Lean_registerReservedNameAction___closed__1);
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_19_ = lean_st_ref_take(v___x_18_);
v___x_20_ = lean_array_push(v___x_19_, v_act_13_);
v___x_21_ = lean_st_ref_put(v___x_18_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT void l_Lean_registerReservedNameAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_13_ = stack[0].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_registerReservedNameAction(v_act_13_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction___boxed(lean_object* v_act_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_registerReservedNameAction(v_act_24_);
return v_res_26_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(32u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((size_t)5ULL);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0);
v___x_35_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_31_);
lean_ctor_set(v___x_35_, 3, v___x_31_);
lean_ctor_set_usize(v___x_35_, 4, v___x_30_);
return v___x_35_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; lean_object* v_traceState_39_; lean_object* v_traces_40_; lean_object* v___x_41_; lean_object* v_traceState_42_; lean_object* v_env_43_; lean_object* v_nextMacroScope_44_; lean_object* v_ngen_45_; lean_object* v_auxDeclNGen_46_; lean_object* v_cache_47_; lean_object* v_recordedDeps_48_; lean_object* v_messages_49_; lean_object* v_infoState_50_; lean_object* v_snapshotTasks_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_70_; 
v___x_38_ = lean_st_ref_get(v___y_36_);
v_traceState_39_ = lean_ctor_get(v___x_38_, 4);
lean_inc_ref(v_traceState_39_);
lean_dec(v___x_38_);
v_traces_40_ = lean_ctor_get(v_traceState_39_, 0);
lean_inc_ref(v_traces_40_);
lean_dec_ref(v_traceState_39_);
v___x_41_ = lean_st_ref_take(v___y_36_);
v_traceState_42_ = lean_ctor_get(v___x_41_, 4);
v_env_43_ = lean_ctor_get(v___x_41_, 0);
v_nextMacroScope_44_ = lean_ctor_get(v___x_41_, 1);
v_ngen_45_ = lean_ctor_get(v___x_41_, 2);
v_auxDeclNGen_46_ = lean_ctor_get(v___x_41_, 3);
v_cache_47_ = lean_ctor_get(v___x_41_, 5);
v_recordedDeps_48_ = lean_ctor_get(v___x_41_, 6);
v_messages_49_ = lean_ctor_get(v___x_41_, 7);
v_infoState_50_ = lean_ctor_get(v___x_41_, 8);
v_snapshotTasks_51_ = lean_ctor_get(v___x_41_, 9);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_70_ == 0)
{
v___x_53_ = v___x_41_;
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_snapshotTasks_51_);
lean_inc(v_infoState_50_);
lean_inc(v_messages_49_);
lean_inc(v_recordedDeps_48_);
lean_inc(v_cache_47_);
lean_inc(v_traceState_42_);
lean_inc(v_auxDeclNGen_46_);
lean_inc(v_ngen_45_);
lean_inc(v_nextMacroScope_44_);
lean_inc(v_env_43_);
lean_dec(v___x_41_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint64_t v_tid_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_68_; 
v_tid_55_ = lean_ctor_get_uint64(v_traceState_42_, sizeof(void*)*1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_traceState_42_);
if (v_isSharedCheck_68_ == 0)
{
lean_object* v_unused_69_; 
v_unused_69_ = lean_ctor_get(v_traceState_42_, 0);
lean_dec(v_unused_69_);
v___x_57_ = v_traceState_42_;
v_isShared_58_ = v_isSharedCheck_68_;
goto v_resetjp_56_;
}
else
{
lean_dec(v_traceState_42_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_68_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_59_);
v___x_61_ = v___x_57_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_59_);
lean_ctor_set_uint64(v_reuseFailAlloc_67_, sizeof(void*)*1, v_tid_55_);
v___x_61_ = v_reuseFailAlloc_67_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___x_61_);
v___x_63_ = v___x_53_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_env_43_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_nextMacroScope_44_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_ngen_45_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v_auxDeclNGen_46_);
lean_ctor_set(v_reuseFailAlloc_66_, 4, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_66_, 5, v_cache_47_);
lean_ctor_set(v_reuseFailAlloc_66_, 6, v_recordedDeps_48_);
lean_ctor_set(v_reuseFailAlloc_66_, 7, v_messages_49_);
lean_ctor_set(v_reuseFailAlloc_66_, 8, v_infoState_50_);
lean_ctor_set(v_reuseFailAlloc_66_, 9, v_snapshotTasks_51_);
v___x_63_ = v_reuseFailAlloc_66_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_st_ref_put(v___y_36_, v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v_traces_40_);
return v___x_65_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_36_ = stack[0].m_obj;
lean_object* v_res_71_;
v_res_71_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_36_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_72_);
lean_dec(v___y_72_);
return v_res_74_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_76_);
return v___x_78_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_75_ = stack[0].m_obj;
lean_object* v___y_76_ = stack[1].m_obj;
lean_object* v_res_79_;
v_res_79_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_75_, v___y_76_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_83_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(lean_object* v_opts_84_, lean_object* v_opt_85_){
_start:
{
lean_object* v_name_86_; lean_object* v_defValue_87_; lean_object* v_map_88_; lean_object* v___x_89_; 
v_name_86_ = lean_ctor_get(v_opt_85_, 0);
v_defValue_87_ = lean_ctor_get(v_opt_85_, 1);
v_map_88_ = lean_ctor_get(v_opts_84_, 0);
v___x_89_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_88_, v_name_86_);
if (lean_obj_tag(v___x_89_) == 0)
{
uint8_t v___x_90_; 
v___x_90_ = lean_unbox(v_defValue_87_);
return v___x_90_;
}
else
{
lean_object* v_val_91_; 
v_val_91_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v___x_89_, 1);
if (lean_obj_tag(v_val_91_) == 1)
{
uint8_t v_v_92_; 
v_v_92_ = lean_ctor_get_uint8(v_val_91_, 0);
lean_dec_ref_known(v_val_91_, 0);
return v_v_92_;
}
else
{
uint8_t v___x_93_; 
lean_dec(v_val_91_);
v___x_93_ = lean_unbox(v_defValue_87_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_84_ = stack[0].m_obj;
lean_object* v_opt_85_ = stack[1].m_obj;
uint8_t v_res_94_;
v_res_94_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_84_, v_opt_85_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_95_, v_opt_96_);
lean_dec_ref(v_opt_96_);
lean_dec_ref(v_opts_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_executeReservedNameAction___lam__0___closed__0));
v___x_101_ = l_Lean_stringToMessageData(v___x_100_);
return v___x_101_;
}
}
lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object* v_name_102_, lean_object* v_x_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lean_executeReservedNameAction___lam__0___closed__1, &l_Lean_executeReservedNameAction___lam__0___closed__1_once, _init_l_Lean_executeReservedNameAction___lam__0___closed__1);
v___x_108_ = l_Lean_MessageData_ofName(v_name_102_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_executeReservedNameAction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_102_ = stack[0].m_obj;
lean_object* v_x_103_ = stack[1].m_obj;
lean_object* v___y_104_ = stack[2].m_obj;
lean_object* v___y_105_ = stack[3].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_executeReservedNameAction___lam__0(v_name_102_, v_x_103_, v___y_104_, v___y_105_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object* v_name_112_, lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_executeReservedNameAction___lam__0(v_name_112_, v_x_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec_ref(v_x_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_inc(v_defValue_121_);
return v_defValue_121_;
}
else
{
lean_object* v_val_124_; 
v_val_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v___x_123_, 1);
if (lean_obj_tag(v_val_124_) == 3)
{
lean_object* v_v_125_; 
v_v_125_ = lean_ctor_get(v_val_124_, 0);
lean_inc(v_v_125_);
lean_dec_ref_known(v_val_124_, 1);
return v_v_125_;
}
else
{
lean_dec(v_val_124_);
lean_inc(v_defValue_121_);
return v_defValue_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(lean_object* v_opts_126_, lean_object* v_opt_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_126_, v_opt_127_);
lean_dec_ref(v_opt_127_);
lean_dec_ref(v_opts_126_);
return v_res_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
lean_ctor_set(v___x_135_, 3, v___x_134_);
lean_ctor_set(v___x_135_, 4, v___x_133_);
lean_ctor_set(v___x_135_, 5, v___x_133_);
lean_ctor_set(v___x_135_, 6, v___x_133_);
lean_ctor_set(v___x_135_, 7, v___x_133_);
lean_ctor_set(v___x_135_, 8, v___x_133_);
lean_ctor_set(v___x_135_, 9, v___x_133_);
lean_ctor_set(v___x_135_, 10, v___x_133_);
lean_ctor_set(v___x_135_, 11, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(32u);
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4(void){
_start:
{
size_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = ((size_t)5ULL);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_unsigned_to_nat(32u);
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_141_);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3);
v___x_144_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_140_);
lean_ctor_set(v___x_144_, 3, v___x_140_);
lean_ctor_set_usize(v___x_144_, 4, v___x_139_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_box(1);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_145_);
return v___x_148_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v_toCold_154_; lean_object* v_env_155_; lean_object* v_options_156_; uint8_t v___x_157_; lean_object* v_env_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_153_ = lean_st_ref_get(v___y_151_);
v_toCold_154_ = lean_ctor_get(v___y_150_, 0);
v_env_155_ = lean_ctor_get(v___x_153_, 0);
lean_inc_ref(v_env_155_);
lean_dec(v___x_153_);
v_options_156_ = lean_ctor_get(v_toCold_154_, 2);
v___x_157_ = 0;
v_env_158_ = l_Lean_Environment_setRecordingDeps(v_env_155_, v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_156_);
v___x_161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_161_, 0, v_env_158_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
lean_ctor_set(v___x_161_, 3, v_options_156_);
v___x_162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_msgData_149_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_149_ = stack[0].m_obj;
lean_object* v___y_150_ = stack[1].m_obj;
lean_object* v___y_151_ = stack[2].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object* v_msgData_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_169_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t v_sz_170_, size_t v_i_171_, lean_object* v_bs_172_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_170_ = stack[0].m_num;
size_t v_i_171_ = stack[1].m_num;
lean_object* v_bs_172_ = stack[2].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_170_, v_i_171_, v_bs_172_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_183_, lean_object* v_i_184_, lean_object* v_bs_185_){
_start:
{
size_t v_sz_boxed_186_; size_t v_i_boxed_187_; lean_object* v_res_188_; 
v_sz_boxed_186_ = lean_unbox_usize(v_sz_183_);
lean_dec(v_sz_183_);
v_i_boxed_187_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_res_188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_boxed_186_, v_i_boxed_187_, v_bs_185_);
return v_res_188_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_oldTraces_189_, lean_object* v_data_190_, lean_object* v_ref_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_toCold_196_; lean_object* v_currRecDepth_197_; lean_object* v_ref_198_; uint16_t v_optionFlags_199_; uint8_t v_suppressElabErrors_200_; uint8_t v_isRecordingDeps_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_traceState_205_; lean_object* v_traces_206_; lean_object* v___x_207_; size_t v_sz_208_; size_t v___x_209_; lean_object* v___x_210_; lean_object* v_msg_211_; lean_object* v___x_212_; lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_251_; 
v_toCold_196_ = lean_ctor_get(v___y_193_, 0);
v_currRecDepth_197_ = lean_ctor_get(v___y_193_, 1);
v_ref_198_ = lean_ctor_get(v___y_193_, 2);
v_optionFlags_199_ = lean_ctor_get_uint16(v___y_193_, sizeof(void*)*3);
v_suppressElabErrors_200_ = lean_ctor_get_uint8(v___y_193_, sizeof(void*)*3 + 2);
v_isRecordingDeps_201_ = lean_ctor_get_uint8(v___y_193_, sizeof(void*)*3 + 3);
v_ref_202_ = l_Lean_replaceRef(v_ref_191_, v_ref_198_);
lean_inc(v_currRecDepth_197_);
lean_inc_ref(v_toCold_196_);
v___x_203_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_203_, 0, v_toCold_196_);
lean_ctor_set(v___x_203_, 1, v_currRecDepth_197_);
lean_ctor_set(v___x_203_, 2, v_ref_202_);
lean_ctor_set_uint16(v___x_203_, sizeof(void*)*3, v_optionFlags_199_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3 + 2, v_suppressElabErrors_200_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3 + 3, v_isRecordingDeps_201_);
v___x_204_ = lean_st_ref_get(v___y_194_);
v_traceState_205_ = lean_ctor_get(v___x_204_, 4);
lean_inc_ref(v_traceState_205_);
lean_dec(v___x_204_);
v_traces_206_ = lean_ctor_get(v_traceState_205_, 0);
lean_inc_ref(v_traces_206_);
lean_dec_ref(v_traceState_205_);
v___x_207_ = l_Lean_PersistentArray_toArray___redArg(v_traces_206_);
lean_dec_ref(v_traces_206_);
v_sz_208_ = lean_array_size(v___x_207_);
v___x_209_ = ((size_t)0ULL);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_208_, v___x_209_, v___x_207_);
v_msg_211_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_211_, 0, v_data_190_);
lean_ctor_set(v_msg_211_, 1, v_msg_192_);
lean_ctor_set(v_msg_211_, 2, v___x_210_);
v___x_212_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_211_, v___x_203_, v___y_194_);
lean_dec_ref_known(v___x_203_, 3);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_251_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_251_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_251_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v_traceState_218_; lean_object* v_env_219_; lean_object* v_nextMacroScope_220_; lean_object* v_ngen_221_; lean_object* v_auxDeclNGen_222_; lean_object* v_cache_223_; lean_object* v_recordedDeps_224_; lean_object* v_messages_225_; lean_object* v_infoState_226_; lean_object* v_snapshotTasks_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_250_; 
v___x_217_ = lean_st_ref_take(v___y_194_);
v_traceState_218_ = lean_ctor_get(v___x_217_, 4);
v_env_219_ = lean_ctor_get(v___x_217_, 0);
v_nextMacroScope_220_ = lean_ctor_get(v___x_217_, 1);
v_ngen_221_ = lean_ctor_get(v___x_217_, 2);
v_auxDeclNGen_222_ = lean_ctor_get(v___x_217_, 3);
v_cache_223_ = lean_ctor_get(v___x_217_, 5);
v_recordedDeps_224_ = lean_ctor_get(v___x_217_, 6);
v_messages_225_ = lean_ctor_get(v___x_217_, 7);
v_infoState_226_ = lean_ctor_get(v___x_217_, 8);
v_snapshotTasks_227_ = lean_ctor_get(v___x_217_, 9);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_250_ == 0)
{
v___x_229_ = v___x_217_;
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snapshotTasks_227_);
lean_inc(v_infoState_226_);
lean_inc(v_messages_225_);
lean_inc(v_recordedDeps_224_);
lean_inc(v_cache_223_);
lean_inc(v_traceState_218_);
lean_inc(v_auxDeclNGen_222_);
lean_inc(v_ngen_221_);
lean_inc(v_nextMacroScope_220_);
lean_inc(v_env_219_);
lean_dec(v___x_217_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
uint64_t v_tid_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_248_; 
v_tid_231_ = lean_ctor_get_uint64(v_traceState_218_, sizeof(void*)*1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_traceState_218_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_traceState_218_, 0);
lean_dec(v_unused_249_);
v___x_233_ = v_traceState_218_;
v_isShared_234_ = v_isSharedCheck_248_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_traceState_218_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_248_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_ref_191_);
lean_ctor_set(v___x_236_, 1, v_a_213_);
v___x_237_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_189_, v___x_236_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_237_);
lean_ctor_set_uint64(v_reuseFailAlloc_247_, sizeof(void*)*1, v_tid_231_);
v___x_239_ = v_reuseFailAlloc_247_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___x_239_);
v___x_241_ = v___x_229_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_env_219_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_nextMacroScope_220_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_ngen_221_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_auxDeclNGen_222_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_cache_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_recordedDeps_224_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_messages_225_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_infoState_226_);
lean_ctor_set(v_reuseFailAlloc_246_, 9, v_snapshotTasks_227_);
v___x_241_ = v_reuseFailAlloc_246_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_st_ref_put(v___y_194_, v___x_241_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_235_);
v___x_244_ = v___x_215_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_235_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_189_ = stack[0].m_obj;
lean_object* v_data_190_ = stack[1].m_obj;
lean_object* v_ref_191_ = stack[2].m_obj;
lean_object* v_msg_192_ = stack[3].m_obj;
lean_object* v___y_193_ = stack[4].m_obj;
lean_object* v___y_194_ = stack[5].m_obj;
lean_object* v_res_252_;
v_res_252_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_189_, v_data_190_, v_ref_191_, v_msg_192_, v___y_193_, v___y_194_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_253_, lean_object* v_data_254_, lean_object* v_ref_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_253_, v_data_254_, v_ref_255_, v_msg_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_260_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v_x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v_x_261_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v_x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 1);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v_x_261_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v_x_261_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v_x_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 0);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_261_ = stack[0].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_261_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_280_);
return v_res_282_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_283_){
_start:
{
if (lean_obj_tag(v_e_283_) == 0)
{
uint8_t v___x_284_; 
v___x_284_ = 2;
return v___x_284_;
}
else
{
lean_object* v_a_285_; uint8_t v___x_286_; 
v_a_285_ = lean_ctor_get(v_e_283_, 0);
v___x_286_ = lean_unbox(v_a_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = 1;
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_283_ = stack[0].m_obj;
uint8_t v_res_289_;
v_res_289_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_283_);
stack->m_num = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_290_);
lean_dec_ref(v_e_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_293_; double v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_float_of_nat(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_298_; double v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1000u);
v___x_299_ = lean_float_of_nat(v___x_298_);
return v___x_299_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_300_, uint8_t v_collapsed_301_, lean_object* v_tag_302_, lean_object* v_opts_303_, uint8_t v_clsEnabled_304_, lean_object* v_oldTraces_305_, lean_object* v_msg_306_, lean_object* v_resStartStop_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_fst_311_; lean_object* v_snd_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v_data_316_; lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___y_332_; lean_object* v_a_333_; uint8_t v___y_348_; double v___y_380_; 
v_fst_311_ = lean_ctor_get(v_resStartStop_307_, 0);
lean_inc(v_fst_311_);
v_snd_312_ = lean_ctor_get(v_resStartStop_307_, 1);
lean_inc(v_snd_312_);
lean_dec_ref(v_resStartStop_307_);
v_fst_327_ = lean_ctor_get(v_snd_312_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v_snd_312_, 1);
lean_inc(v_snd_328_);
lean_dec(v_snd_312_);
v___x_329_ = l_Lean_trace_profiler;
v___x_330_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_303_, v___x_329_);
if (v___x_330_ == 0)
{
v___y_348_ = v___x_330_;
goto v___jp_347_;
}
else
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = l_Lean_trace_profiler_useHeartbeats;
v___x_386_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_303_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; double v___x_389_; double v___x_390_; double v___x_391_; 
v___x_387_ = l_Lean_trace_profiler_threshold;
v___x_388_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_303_, v___x_387_);
v___x_389_ = lean_float_of_nat(v___x_388_);
v___x_390_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_391_ = lean_float_div(v___x_389_, v___x_390_);
v___y_380_ = v___x_391_;
goto v___jp_379_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; double v___x_394_; 
v___x_392_ = l_Lean_trace_profiler_threshold;
v___x_393_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_303_, v___x_392_);
v___x_394_ = lean_float_of_nat(v___x_393_);
v___y_380_ = v___x_394_;
goto v___jp_379_;
}
}
v___jp_313_:
{
lean_object* v___x_317_; 
lean_inc(v___y_315_);
v___x_317_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_305_, v_data_316_, v___y_315_, v___y_314_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; 
lean_dec_ref_known(v___x_317_, 1);
v___x_318_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_311_);
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_fst_311_);
v_a_319_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_317_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
v___jp_331_:
{
uint8_t v_result_334_; lean_object* v___x_335_; lean_object* v___x_336_; double v___x_337_; lean_object* v_data_338_; 
v_result_334_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_311_);
v___x_335_ = lean_box(v_result_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
lean_inc_ref(v_tag_302_);
lean_inc_ref(v___x_336_);
lean_inc(v_cls_300_);
v_data_338_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_338_, 0, v_cls_300_);
lean_ctor_set(v_data_338_, 1, v___x_336_);
lean_ctor_set(v_data_338_, 2, v_tag_302_);
lean_ctor_set_float(v_data_338_, sizeof(void*)*3, v___x_337_);
lean_ctor_set_float(v_data_338_, sizeof(void*)*3 + 8, v___x_337_);
lean_ctor_set_uint8(v_data_338_, sizeof(void*)*3 + 16, v_collapsed_301_);
if (v___x_330_ == 0)
{
lean_dec_ref_known(v___x_336_, 1);
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
lean_dec_ref(v_tag_302_);
lean_dec(v_cls_300_);
v___y_314_ = v_a_333_;
v___y_315_ = v___y_332_;
v_data_316_ = v_data_338_;
goto v___jp_313_;
}
else
{
lean_object* v_data_339_; double v___x_340_; double v___x_341_; 
lean_dec_ref_known(v_data_338_, 3);
v_data_339_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_339_, 0, v_cls_300_);
lean_ctor_set(v_data_339_, 1, v___x_336_);
lean_ctor_set(v_data_339_, 2, v_tag_302_);
v___x_340_ = lean_unbox_float(v_fst_327_);
lean_dec(v_fst_327_);
lean_ctor_set_float(v_data_339_, sizeof(void*)*3, v___x_340_);
v___x_341_ = lean_unbox_float(v_snd_328_);
lean_dec(v_snd_328_);
lean_ctor_set_float(v_data_339_, sizeof(void*)*3 + 8, v___x_341_);
lean_ctor_set_uint8(v_data_339_, sizeof(void*)*3 + 16, v_collapsed_301_);
v___y_314_ = v_a_333_;
v___y_315_ = v___y_332_;
v_data_316_ = v_data_339_;
goto v___jp_313_;
}
}
v___jp_342_:
{
lean_object* v_ref_343_; lean_object* v___x_344_; 
v_ref_343_ = lean_ctor_get(v___y_308_, 2);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v_fst_311_);
v___x_344_ = lean_apply_4(v_msg_306_, v_fst_311_, v___y_308_, v___y_309_, lean_box(0));
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___y_332_ = v_ref_343_;
v_a_333_ = v_a_345_;
goto v___jp_331_;
}
else
{
lean_object* v___x_346_; 
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
v___y_332_ = v_ref_343_;
v_a_333_ = v___x_346_;
goto v___jp_331_;
}
}
v___jp_347_:
{
if (v_clsEnabled_304_ == 0)
{
if (v___y_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_traceState_350_; lean_object* v_env_351_; lean_object* v_nextMacroScope_352_; lean_object* v_ngen_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_cache_355_; lean_object* v_recordedDeps_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
lean_dec_ref(v_msg_306_);
lean_dec_ref(v_tag_302_);
lean_dec(v_cls_300_);
v___x_349_ = lean_st_ref_take(v___y_309_);
v_traceState_350_ = lean_ctor_get(v___x_349_, 4);
v_env_351_ = lean_ctor_get(v___x_349_, 0);
v_nextMacroScope_352_ = lean_ctor_get(v___x_349_, 1);
v_ngen_353_ = lean_ctor_get(v___x_349_, 2);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_349_, 3);
v_cache_355_ = lean_ctor_get(v___x_349_, 5);
v_recordedDeps_356_ = lean_ctor_get(v___x_349_, 6);
v_messages_357_ = lean_ctor_get(v___x_349_, 7);
v_infoState_358_ = lean_ctor_get(v___x_349_, 8);
v_snapshotTasks_359_ = lean_ctor_get(v___x_349_, 9);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_378_ == 0)
{
v___x_361_ = v___x_349_;
v_isShared_362_ = v_isSharedCheck_378_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_recordedDeps_356_);
lean_inc(v_cache_355_);
lean_inc(v_traceState_350_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_ngen_353_);
lean_inc(v_nextMacroScope_352_);
lean_inc(v_env_351_);
lean_dec(v___x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_378_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
uint64_t v_tid_363_; lean_object* v_traces_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_377_; 
v_tid_363_ = lean_ctor_get_uint64(v_traceState_350_, sizeof(void*)*1);
v_traces_364_ = lean_ctor_get(v_traceState_350_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_traceState_350_);
if (v_isSharedCheck_377_ == 0)
{
v___x_366_ = v_traceState_350_;
v_isShared_367_ = v_isSharedCheck_377_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_traces_364_);
lean_dec(v_traceState_350_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_377_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_305_, v_traces_364_);
lean_dec_ref(v_traces_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_368_);
lean_ctor_set_uint64(v_reuseFailAlloc_376_, sizeof(void*)*1, v_tid_363_);
v___x_370_ = v_reuseFailAlloc_376_;
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
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_env_351_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_nextMacroScope_352_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_ngen_353_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_cache_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 6, v_recordedDeps_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 7, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 8, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_375_, 9, v_snapshotTasks_359_);
v___x_372_ = v_reuseFailAlloc_375_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_st_ref_put(v___y_309_, v___x_372_);
v___x_374_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_311_);
return v___x_374_;
}
}
}
}
}
else
{
goto v___jp_342_;
}
}
else
{
goto v___jp_342_;
}
}
v___jp_379_:
{
double v___x_381_; double v___x_382_; double v___x_383_; uint8_t v___x_384_; 
v___x_381_ = lean_unbox_float(v_snd_328_);
v___x_382_ = lean_unbox_float(v_fst_327_);
v___x_383_ = lean_float_sub(v___x_381_, v___x_382_);
v___x_384_ = lean_float_decLt(v___y_380_, v___x_383_);
v___y_348_ = v___x_384_;
goto v___jp_347_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_300_ = stack[0].m_obj;
uint8_t v_collapsed_301_ = stack[1].m_num;
lean_object* v_tag_302_ = stack[2].m_obj;
lean_object* v_opts_303_ = stack[3].m_obj;
uint8_t v_clsEnabled_304_ = stack[4].m_num;
lean_object* v_oldTraces_305_ = stack[5].m_obj;
lean_object* v_msg_306_ = stack[6].m_obj;
lean_object* v_resStartStop_307_ = stack[7].m_obj;
lean_object* v___y_308_ = stack[8].m_obj;
lean_object* v___y_309_ = stack[9].m_obj;
lean_object* v_res_395_;
v_res_395_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_300_, v_collapsed_301_, v_tag_302_, v_opts_303_, v_clsEnabled_304_, v_oldTraces_305_, v_msg_306_, v_resStartStop_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_396_, lean_object* v_collapsed_397_, lean_object* v_tag_398_, lean_object* v_opts_399_, lean_object* v_clsEnabled_400_, lean_object* v_oldTraces_401_, lean_object* v_msg_402_, lean_object* v_resStartStop_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v_collapsed_boxed_407_; uint8_t v_clsEnabled_boxed_408_; lean_object* v_res_409_; 
v_collapsed_boxed_407_ = lean_unbox(v_collapsed_397_);
v_clsEnabled_boxed_408_ = lean_unbox(v_clsEnabled_400_);
v_res_409_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_396_, v_collapsed_boxed_407_, v_tag_398_, v_opts_399_, v_clsEnabled_boxed_408_, v_oldTraces_401_, v_msg_402_, v_resStartStop_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec_ref(v_opts_399_);
return v_res_409_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_410_, lean_object* v_as_411_, size_t v_i_412_, size_t v_stop_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_eq(v_i_412_, v_stop_413_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; lean_object* v___x_5263__overap_419_; lean_object* v___x_420_; 
v___x_418_ = 1;
v___x_5263__overap_419_ = lean_array_uget_borrowed(v_as_411_, v_i_412_);
lean_inc(v___x_5263__overap_419_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
lean_inc(v_name_410_);
v___x_420_ = lean_apply_4(v___x_5263__overap_419_, v_name_410_, v___y_414_, v___y_415_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_433_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v___x_425_; 
v___x_425_ = lean_unbox(v_a_421_);
lean_dec(v_a_421_);
if (v___x_425_ == 0)
{
size_t v___x_426_; size_t v___x_427_; 
lean_del_object(v___x_423_);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_412_, v___x_426_);
v_i_412_ = v___x_427_;
goto _start;
}
else
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v_name_410_);
v___x_429_ = lean_box(v___x_418_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_431_ = v___x_423_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_dec(v_name_410_);
return v___x_420_;
}
}
else
{
uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_name_410_);
v___x_434_ = 0;
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_410_ = stack[0].m_obj;
lean_object* v_as_411_ = stack[1].m_obj;
size_t v_i_412_ = stack[2].m_num;
size_t v_stop_413_ = stack[3].m_num;
lean_object* v___y_414_ = stack[4].m_obj;
lean_object* v___y_415_ = stack[5].m_obj;
lean_object* v_res_437_;
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_410_, v_as_411_, v_i_412_, v_stop_413_, v___y_414_, v___y_415_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_438_, lean_object* v_as_439_, lean_object* v_i_440_, lean_object* v_stop_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
size_t v_i_boxed_445_; size_t v_stop_boxed_446_; lean_object* v_res_447_; 
v_i_boxed_445_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_stop_boxed_446_ = lean_unbox_usize(v_stop_441_);
lean_dec(v_stop_441_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_438_, v_as_439_, v_i_boxed_445_, v_stop_boxed_446_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec_ref(v_as_439_);
return v_res_447_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_456_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_457_ = l_Lean_Name_append(v___x_456_, v___x_455_);
return v___x_457_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1000000000u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_toCold_464_; lean_object* v_options_465_; lean_object* v_inheritedTraceOptions_466_; uint8_t v_hasTrace_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___y_471_; 
v_toCold_464_ = lean_ctor_get(v_a_461_, 0);
v_options_465_ = lean_ctor_get(v_toCold_464_, 2);
v_inheritedTraceOptions_466_ = lean_ctor_get(v_toCold_464_, 11);
v_hasTrace_467_ = lean_ctor_get_uint8(v_options_465_, sizeof(void*)*1);
v___x_468_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_469_ = lean_box(0);
if (v_hasTrace_467_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_488_ = lean_st_ref_get(v___x_468_);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_array_get_size(v___x_488_);
v___x_491_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
lean_dec(v___x_488_);
lean_dec(v_name_460_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_469_);
return v___x_492_;
}
else
{
if (v___x_491_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v___x_488_);
lean_dec(v_name_460_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_469_);
return v___x_493_;
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_usize_of_nat(v___x_490_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_460_, v___x_488_, v___x_494_, v___x_495_, v_a_461_, v_a_462_);
lean_dec(v___x_488_);
v___y_471_ = v___x_496_;
goto v___jp_470_;
}
}
}
else
{
lean_object* v___f_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v_a_505_; lean_object* v___y_518_; lean_object* v___y_519_; uint8_t v_a_520_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v_a_526_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v_a_538_; 
lean_inc(v_name_460_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_497_, 0, v_name_460_);
v___x_498_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_499_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_500_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_466_, v_options_465_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = l_Lean_trace_profiler;
v___x_583_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_465_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
lean_dec_ref(v___f_497_);
v___x_584_ = lean_st_ref_get(v___x_468_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_array_get_size(v___x_584_);
v___x_587_ = lean_nat_dec_lt(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v___x_584_);
lean_dec(v_name_460_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_469_);
return v___x_588_;
}
else
{
if (v___x_587_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v___x_584_);
lean_dec(v_name_460_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_469_);
return v___x_589_;
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((size_t)0ULL);
v___x_591_ = lean_usize_of_nat(v___x_586_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_460_, v___x_584_, v___x_590_, v___x_591_, v_a_461_, v_a_462_);
lean_dec(v___x_584_);
v___y_471_ = v___x_592_;
goto v___jp_470_;
}
}
}
else
{
goto v___jp_541_;
}
}
else
{
goto v___jp_541_;
}
v___jp_502_:
{
lean_object* v___x_506_; double v___x_507_; double v___x_508_; double v___x_509_; double v___x_510_; double v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_506_ = lean_io_mono_nanos_now();
v___x_507_ = lean_float_of_nat(v___y_504_);
v___x_508_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_509_ = lean_float_div(v___x_507_, v___x_508_);
v___x_510_ = lean_float_of_nat(v___x_506_);
v___x_511_ = lean_float_div(v___x_510_, v___x_508_);
v___x_512_ = lean_box_float(v___x_509_);
v___x_513_ = lean_box_float(v___x_511_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_a_505_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_498_, v_hasTrace_467_, v___x_499_, v_options_465_, v___x_501_, v___y_503_, v___f_497_, v___x_515_, v_a_461_, v_a_462_);
v___y_471_ = v___x_516_;
goto v___jp_470_;
}
v___jp_517_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(v_a_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___y_503_ = v___y_518_;
v___y_504_ = v___y_519_;
v_a_505_ = v___x_522_;
goto v___jp_502_;
}
v___jp_523_:
{
lean_object* v___x_527_; double v___x_528_; double v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_527_ = lean_io_get_num_heartbeats();
v___x_528_ = lean_float_of_nat(v___y_525_);
v___x_529_ = lean_float_of_nat(v___x_527_);
v___x_530_ = lean_box_float(v___x_528_);
v___x_531_ = lean_box_float(v___x_529_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_a_526_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_498_, v_hasTrace_467_, v___x_499_, v_options_465_, v___x_501_, v___y_524_, v___f_497_, v___x_533_, v_a_461_, v_a_462_);
v___y_471_ = v___x_534_;
goto v___jp_470_;
}
v___jp_535_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(v_a_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___y_524_ = v___y_536_;
v___y_525_ = v___y_537_;
v_a_526_ = v___x_540_;
goto v___jp_523_;
}
v___jp_541_:
{
lean_object* v___x_542_; lean_object* v_a_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_462_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
v___x_544_ = l_Lean_trace_profiler_useHeartbeats;
v___x_545_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_465_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_546_ = lean_io_mono_nanos_now();
v___x_547_ = lean_st_ref_get(v___x_468_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_array_get_size(v___x_547_);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v___x_547_);
lean_dec(v_name_460_);
v___y_518_ = v_a_543_;
v___y_519_ = v___x_546_;
v_a_520_ = v___x_550_;
goto v___jp_517_;
}
else
{
if (v___x_550_ == 0)
{
lean_dec(v___x_547_);
lean_dec(v_name_460_);
v___y_518_ = v_a_543_;
v___y_519_ = v___x_546_;
v_a_520_ = v___x_550_;
goto v___jp_517_;
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_549_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_460_, v___x_547_, v___x_551_, v___x_552_, v_a_461_, v_a_462_);
lean_dec(v___x_547_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
v___y_518_ = v_a_543_;
v___y_519_ = v___x_546_;
v_a_520_ = v___x_555_;
goto v___jp_517_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_503_ = v_a_543_;
v___y_504_ = v___x_546_;
v_a_505_ = v___x_561_;
goto v___jp_502_;
}
}
}
}
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_564_ = lean_io_get_num_heartbeats();
v___x_565_ = lean_st_ref_get(v___x_468_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_array_get_size(v___x_565_);
v___x_568_ = lean_nat_dec_lt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v___x_565_);
lean_dec(v_name_460_);
v___y_536_ = v_a_543_;
v___y_537_ = v___x_564_;
v_a_538_ = v___x_568_;
goto v___jp_535_;
}
else
{
if (v___x_568_ == 0)
{
lean_dec(v___x_565_);
lean_dec(v_name_460_);
v___y_536_ = v_a_543_;
v___y_537_ = v___x_564_;
v_a_538_ = v___x_568_;
goto v___jp_535_;
}
else
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)0ULL);
v___x_570_ = lean_usize_of_nat(v___x_567_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_460_, v___x_565_, v___x_569_, v___x_570_, v_a_461_, v_a_462_);
lean_dec(v___x_565_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; uint8_t v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
v___y_536_ = v_a_543_;
v___y_537_ = v___x_564_;
v_a_538_ = v___x_573_;
goto v___jp_535_;
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_571_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_571_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
v___y_524_ = v_a_543_;
v___y_525_ = v___x_564_;
v_a_526_ = v___x_579_;
goto v___jp_523_;
}
}
}
}
}
}
}
}
v___jp_470_:
{
if (lean_obj_tag(v___y_471_) == 0)
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_isSharedCheck_478_ = !lean_is_exclusive(v___y_471_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___y_471_, 0);
lean_dec(v_unused_479_);
v___x_473_ = v___y_471_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_dec(v___y_471_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_469_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_469_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_a_480_ = lean_ctor_get(v___y_471_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___y_471_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___y_471_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___y_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_executeReservedNameAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_460_ = stack[0].m_obj;
lean_object* v_a_461_ = stack[1].m_obj;
lean_object* v_a_462_ = stack[2].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_executeReservedNameAction(v_name_460_, v_a_461_, v_a_462_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_executeReservedNameAction(v_name_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_598_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_600_);
return v___x_604_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_600_ = stack[1].m_obj;
lean_object* v___y_601_ = stack[2].m_obj;
lean_object* v___y_602_ = stack[3].m_obj;
lean_object* v_res_605_;
v_res_605_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_box(0), v_x_600_, v___y_601_, v___y_602_);
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_606_, lean_object* v_x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_606_, v_x_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_611_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_619_, uint8_t v___y_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_621_) == 1)
{
lean_object* v_pre_622_; 
v_pre_622_ = lean_ctor_get(v_x_621_, 0);
switch(lean_obj_tag(v_pre_622_))
{
case 1:
{
lean_object* v_pre_623_; 
v_pre_623_ = lean_ctor_get(v_pre_622_, 0);
switch(lean_obj_tag(v_pre_623_))
{
case 0:
{
lean_object* v_str_624_; lean_object* v_str_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_str_624_ = lean_ctor_get(v_x_621_, 1);
v_str_625_ = lean_ctor_get(v_pre_622_, 1);
v___x_626_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_627_ = lean_string_dec_eq(v_str_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_629_ = lean_string_dec_eq(v_str_625_, v___x_628_);
if (v___x_629_ == 0)
{
return v___x_629_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_631_ = lean_string_dec_eq(v_str_624_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
return v_suppressElabErrors_619_;
}
}
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_633_ = lean_string_dec_eq(v_str_624_, v___x_632_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
return v_suppressElabErrors_619_;
}
}
}
case 1:
{
lean_object* v_pre_634_; 
v_pre_634_ = lean_ctor_get(v_pre_623_, 0);
if (lean_obj_tag(v_pre_634_) == 0)
{
lean_object* v_str_635_; lean_object* v_str_636_; lean_object* v_str_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_str_635_ = lean_ctor_get(v_x_621_, 1);
v_str_636_ = lean_ctor_get(v_pre_622_, 1);
v_str_637_ = lean_ctor_get(v_pre_623_, 1);
v___x_638_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_639_ = lean_string_dec_eq(v_str_637_, v___x_638_);
if (v___x_639_ == 0)
{
return v___x_639_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_641_ = lean_string_dec_eq(v_str_636_, v___x_640_);
if (v___x_641_ == 0)
{
return v___x_641_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_643_ = lean_string_dec_eq(v_str_635_, v___x_642_);
if (v___x_643_ == 0)
{
return v___x_643_;
}
else
{
return v_suppressElabErrors_619_;
}
}
}
}
else
{
return v___y_620_;
}
}
default: 
{
return v___y_620_;
}
}
}
case 0:
{
lean_object* v_str_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_str_644_ = lean_ctor_get(v_x_621_, 1);
v___x_645_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_646_ = lean_string_dec_eq(v_str_644_, v___x_645_);
if (v___x_646_ == 0)
{
return v___x_646_;
}
else
{
return v_suppressElabErrors_619_;
}
}
default: 
{
return v___y_620_;
}
}
}
else
{
return v___y_620_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_619_ = stack[0].m_num;
uint8_t v___y_620_ = stack[1].m_num;
lean_object* v_x_621_ = stack[2].m_obj;
uint8_t v_res_647_;
v_res_647_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_619_, v___y_620_, v_x_621_);
stack->m_num = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_648_, lean_object* v___y_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_suppressElabErrors_boxed_651_; uint8_t v___y_5030__boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_suppressElabErrors_boxed_651_ = lean_unbox(v_suppressElabErrors_648_);
v___y_5030__boxed_652_ = lean_unbox(v___y_649_);
v_res_653_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_651_, v___y_5030__boxed_652_, v_x_650_);
lean_dec(v_x_650_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_655_, lean_object* v_msgData_656_, uint8_t v_severity_657_, uint8_t v_isSilent_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; uint8_t v___y_668_; lean_object* v___y_669_; lean_object* v_toCold_670_; lean_object* v___y_671_; lean_object* v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_737_; uint8_t v___y_738_; uint8_t v___y_739_; uint8_t v___x_750_; uint8_t v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; uint8_t v___y_756_; uint8_t v___x_764_; 
v___x_750_ = 2;
v___x_764_ = l_Lean_instBEqMessageSeverity_beq(v_severity_657_, v___x_750_);
if (v___x_764_ == 0)
{
v___y_756_ = v___x_764_;
goto v___jp_755_;
}
else
{
uint8_t v___x_765_; 
lean_inc_ref(v_msgData_656_);
v___x_765_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_656_);
v___y_756_ = v___x_765_;
goto v___jp_755_;
}
v___jp_662_:
{
lean_object* v_currNamespace_672_; lean_object* v_openDecls_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_env_678_; lean_object* v_nextMacroScope_679_; lean_object* v_ngen_680_; lean_object* v_auxDeclNGen_681_; lean_object* v_traceState_682_; lean_object* v_cache_683_; lean_object* v_recordedDeps_684_; lean_object* v_messages_685_; lean_object* v_infoState_686_; lean_object* v_snapshotTasks_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
v_currNamespace_672_ = lean_ctor_get(v_toCold_670_, 4);
v_openDecls_673_ = lean_ctor_get(v_toCold_670_, 5);
lean_inc(v_openDecls_673_);
lean_inc(v_currNamespace_672_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_currNamespace_672_);
lean_ctor_set(v___x_674_, 1, v_openDecls_673_);
v___x_675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___y_664_);
lean_inc_ref(v___y_669_);
lean_inc_ref(v___y_663_);
v___x_676_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_676_, 0, v___y_663_);
lean_ctor_set(v___x_676_, 1, v___y_667_);
lean_ctor_set(v___x_676_, 2, v___y_665_);
lean_ctor_set(v___x_676_, 3, v___y_669_);
lean_ctor_set(v___x_676_, 4, v___x_675_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*5, v___y_668_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*5 + 1, v___y_666_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*5 + 2, v_isSilent_658_);
v___x_677_ = lean_st_ref_take(v___y_671_);
v_env_678_ = lean_ctor_get(v___x_677_, 0);
v_nextMacroScope_679_ = lean_ctor_get(v___x_677_, 1);
v_ngen_680_ = lean_ctor_get(v___x_677_, 2);
v_auxDeclNGen_681_ = lean_ctor_get(v___x_677_, 3);
v_traceState_682_ = lean_ctor_get(v___x_677_, 4);
v_cache_683_ = lean_ctor_get(v___x_677_, 5);
v_recordedDeps_684_ = lean_ctor_get(v___x_677_, 6);
v_messages_685_ = lean_ctor_get(v___x_677_, 7);
v_infoState_686_ = lean_ctor_get(v___x_677_, 8);
v_snapshotTasks_687_ = lean_ctor_get(v___x_677_, 9);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_698_ == 0)
{
v___x_689_ = v___x_677_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snapshotTasks_687_);
lean_inc(v_infoState_686_);
lean_inc(v_messages_685_);
lean_inc(v_recordedDeps_684_);
lean_inc(v_cache_683_);
lean_inc(v_traceState_682_);
lean_inc(v_auxDeclNGen_681_);
lean_inc(v_ngen_680_);
lean_inc(v_nextMacroScope_679_);
lean_inc(v_env_678_);
lean_dec(v___x_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = lean_box(0);
v___x_692_ = l_Lean_MessageLog_add(v___x_676_, v_messages_685_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 7, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_env_678_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_nextMacroScope_679_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_ngen_680_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_auxDeclNGen_681_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_traceState_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v_cache_683_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v_recordedDeps_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_697_, 8, v_infoState_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 9, v_snapshotTasks_687_);
v___x_694_ = v_reuseFailAlloc_697_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_st_ref_put(v___y_671_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
return v___x_696_;
}
}
}
v___jp_699_:
{
lean_object* v_fileName_708_; lean_object* v_fileMap_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_725_; 
v_fileName_708_ = lean_ctor_get(v___y_704_, 0);
v_fileMap_709_ = lean_ctor_get(v___y_704_, 1);
v___x_710_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_656_);
v___x_711_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_710_, v___y_659_, v___y_660_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_725_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_725_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_725_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_inc_ref_n(v_fileMap_709_, 2);
v___x_716_ = l_Lean_FileMap_toPosition(v_fileMap_709_, v___y_706_);
lean_dec(v___y_706_);
v___x_717_ = l_Lean_FileMap_toPosition(v_fileMap_709_, v___y_707_);
lean_dec(v___y_707_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_705_ == 0)
{
lean_del_object(v___x_714_);
lean_dec_ref(v___y_700_);
v___y_663_ = v_fileName_708_;
v___y_664_ = v_a_712_;
v___y_665_ = v___x_718_;
v___y_666_ = v___y_702_;
v___y_667_ = v___x_716_;
v___y_668_ = v___y_703_;
v___y_669_ = v___x_719_;
v_toCold_670_ = v___y_701_;
v___y_671_ = v___y_660_;
goto v___jp_662_;
}
else
{
uint8_t v___x_720_; 
lean_inc(v_a_712_);
v___x_720_ = l_Lean_MessageData_hasTag(v___y_700_, v_a_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec_ref_known(v___x_718_, 1);
lean_dec_ref(v___x_716_);
lean_dec(v_a_712_);
v___x_721_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_721_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_del_object(v___x_714_);
v___y_663_ = v_fileName_708_;
v___y_664_ = v_a_712_;
v___y_665_ = v___x_718_;
v___y_666_ = v___y_702_;
v___y_667_ = v___x_716_;
v___y_668_ = v___y_703_;
v___y_669_ = v___x_719_;
v_toCold_670_ = v___y_701_;
v___y_671_ = v___y_660_;
goto v___jp_662_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Syntax_getTailPos_x3f(v___y_730_, v___y_732_);
lean_dec(v___y_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_inc(v___y_733_);
v___y_700_ = v___y_727_;
v___y_701_ = v___y_728_;
v___y_702_ = v___y_731_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_728_;
v___y_705_ = v___y_729_;
v___y_706_ = v___y_733_;
v___y_707_ = v___y_733_;
goto v___jp_699_;
}
else
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___y_700_ = v___y_727_;
v___y_701_ = v___y_728_;
v___y_702_ = v___y_731_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_728_;
v___y_705_ = v___y_729_;
v___y_706_ = v___y_733_;
v___y_707_ = v_val_735_;
goto v___jp_699_;
}
}
v___jp_736_:
{
lean_object* v_toCold_740_; lean_object* v_ref_741_; uint8_t v_suppressElabErrors_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v_ref_746_; lean_object* v___x_747_; 
v_toCold_740_ = lean_ctor_get(v___y_659_, 0);
v_ref_741_ = lean_ctor_get(v___y_659_, 2);
v_suppressElabErrors_742_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 2);
v___x_743_ = lean_box(v_suppressElabErrors_742_);
v___x_744_ = lean_box(v___y_737_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_745_, 0, v___x_743_);
lean_closure_set(v___f_745_, 1, v___x_744_);
v_ref_746_ = l_Lean_replaceRef(v_ref_655_, v_ref_741_);
v___x_747_ = l_Lean_Syntax_getPos_x3f(v_ref_746_, v___y_738_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___y_727_ = v___f_745_;
v___y_728_ = v_toCold_740_;
v___y_729_ = v_suppressElabErrors_742_;
v___y_730_ = v_ref_746_;
v___y_731_ = v___y_739_;
v___y_732_ = v___y_738_;
v___y_733_ = v___x_748_;
goto v___jp_726_;
}
else
{
lean_object* v_val_749_; 
v_val_749_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v___x_747_, 1);
v___y_727_ = v___f_745_;
v___y_728_ = v_toCold_740_;
v___y_729_ = v_suppressElabErrors_742_;
v___y_730_ = v_ref_746_;
v___y_731_ = v___y_739_;
v___y_732_ = v___y_738_;
v___y_733_ = v_val_749_;
goto v___jp_726_;
}
}
v___jp_751_:
{
if (v___y_754_ == 0)
{
v___y_737_ = v___y_752_;
v___y_738_ = v___y_753_;
v___y_739_ = v_severity_657_;
goto v___jp_736_;
}
else
{
v___y_737_ = v___y_752_;
v___y_738_ = v___y_753_;
v___y_739_ = v___x_750_;
goto v___jp_736_;
}
}
v___jp_755_:
{
if (v___y_756_ == 0)
{
uint8_t v___x_757_; uint8_t v___x_758_; 
v___x_757_ = 1;
v___x_758_ = l_Lean_instBEqMessageSeverity_beq(v_severity_657_, v___x_757_);
if (v___x_758_ == 0)
{
v___y_752_ = v___y_756_;
v___y_753_ = v___y_756_;
v___y_754_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_659_);
v___x_760_ = l_Lean_warningAsError;
v___x_761_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_759_, v___x_760_);
lean_dec_ref(v___x_759_);
v___y_752_ = v___y_756_;
v___y_753_ = v___y_756_;
v___y_754_ = v___x_761_;
goto v___jp_751_;
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref(v_msgData_656_);
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_655_ = stack[0].m_obj;
lean_object* v_msgData_656_ = stack[1].m_obj;
uint8_t v_severity_657_ = stack[2].m_num;
uint8_t v_isSilent_658_ = stack[3].m_num;
lean_object* v___y_659_ = stack[4].m_obj;
lean_object* v___y_660_ = stack[5].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_655_, v_msgData_656_, v_severity_657_, v_isSilent_658_, v___y_659_, v___y_660_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_767_, lean_object* v_msgData_768_, lean_object* v_severity_769_, lean_object* v_isSilent_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_severity_boxed_774_; uint8_t v_isSilent_boxed_775_; lean_object* v_res_776_; 
v_severity_boxed_774_ = lean_unbox(v_severity_769_);
v_isSilent_boxed_775_ = lean_unbox(v_isSilent_770_);
v_res_776_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_767_, v_msgData_768_, v_severity_boxed_774_, v_isSilent_boxed_775_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v_ref_767_);
return v_res_776_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_777_, uint8_t v_severity_778_, uint8_t v_isSilent_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_ref_783_; lean_object* v___x_784_; 
v_ref_783_ = lean_ctor_get(v___y_780_, 2);
v___x_784_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_783_, v_msgData_777_, v_severity_778_, v_isSilent_779_, v___y_780_, v___y_781_);
return v___x_784_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_777_ = stack[0].m_obj;
uint8_t v_severity_778_ = stack[1].m_num;
uint8_t v_isSilent_779_ = stack[2].m_num;
lean_object* v___y_780_ = stack[3].m_obj;
lean_object* v___y_781_ = stack[4].m_obj;
lean_object* v_res_785_;
v_res_785_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_777_, v_severity_778_, v_isSilent_779_, v___y_780_, v___y_781_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_786_, lean_object* v_severity_787_, lean_object* v_isSilent_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_severity_boxed_792_; uint8_t v_isSilent_boxed_793_; lean_object* v_res_794_; 
v_severity_boxed_792_ = lean_unbox(v_severity_787_);
v_isSilent_boxed_793_ = lean_unbox(v_isSilent_788_);
v_res_794_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_786_, v_severity_boxed_792_, v_isSilent_boxed_793_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
v___x_799_ = 2;
v___x_800_ = 0;
v___x_801_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_795_, v___x_799_, v___x_800_, v___y_796_, v___y_797_);
return v___x_801_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_realizeGlobalName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_795_ = stack[0].m_obj;
lean_object* v___y_796_ = stack[1].m_obj;
lean_object* v___y_797_ = stack[2].m_obj;
lean_object* v_res_802_;
v_res_802_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_795_, v___y_796_, v___y_797_);
stack->m_obj
 = v_res_802_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_807_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v___x_820_; 
lean_dec(v_id_814_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_x_816_);
return v___x_820_;
}
else
{
lean_object* v_head_821_; lean_object* v_tail_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_873_; 
v_head_821_ = lean_ctor_get(v_x_815_, 0);
v_tail_822_ = lean_ctor_get(v_x_815_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_873_ == 0)
{
v___x_824_ = v_x_815_;
v_isShared_825_ = v_isSharedCheck_873_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_tail_822_);
lean_inc(v_head_821_);
lean_dec(v_x_815_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_873_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___y_827_; uint8_t v___y_828_; uint8_t v_a_854_; lean_object* v_fst_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v_env_859_; uint8_t v___x_860_; uint8_t v___y_862_; 
v_fst_856_ = lean_ctor_get(v_head_821_, 0);
v___x_857_ = 1;
v___x_858_ = lean_st_ref_get(v___y_818_);
v_env_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_ref_n(v_env_859_, 2);
lean_dec(v___x_858_);
lean_inc(v_fst_856_);
v___x_860_ = l_Lean_Environment_contains(v_env_859_, v_fst_856_, v___x_857_);
if (v___x_860_ == 0)
{
uint8_t v_isExporting_870_; 
v_isExporting_870_ = lean_ctor_get_uint8(v_env_859_, sizeof(void*)*13);
if (v_isExporting_870_ == 0)
{
lean_dec_ref(v_env_859_);
v___y_862_ = v___x_860_;
goto v___jp_861_;
}
else
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = l_Lean_Environment_setExporting(v_env_859_, v___x_860_);
v___x_872_ = l_Lean_Environment_isImportedConst(v___x_871_, v_fst_856_);
lean_dec_ref(v___x_871_);
v___y_862_ = v___x_872_;
goto v___jp_861_;
}
}
else
{
lean_dec_ref(v_env_859_);
goto v___jp_848_;
}
v___jp_826_:
{
if (v___y_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_829_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_814_);
v___x_830_ = l_Lean_MessageData_ofName(v_id_814_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_Exception_toMessageData(v___y_827_);
v___x_835_ = l_Lean_indentD(v___x_834_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_833_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_836_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_dec_ref_known(v___x_837_, 1);
v_x_815_ = v_tail_822_;
goto _start;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_tail_822_);
lean_dec(v_x_816_);
lean_dec(v_id_814_);
v_a_839_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v_tail_822_);
lean_dec(v_x_816_);
lean_dec(v_id_814_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___y_827_);
return v___x_847_;
}
}
v___jp_848_:
{
lean_object* v___x_850_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v_x_816_);
v___x_850_ = v___x_824_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_head_821_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_x_816_);
v___x_850_ = v_reuseFailAlloc_852_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v_x_815_ = v_tail_822_;
v_x_816_ = v___x_850_;
goto _start;
}
}
v___jp_853_:
{
if (v_a_854_ == 0)
{
lean_del_object(v___x_824_);
lean_dec(v_head_821_);
v_x_815_ = v_tail_822_;
goto _start;
}
else
{
goto v___jp_848_;
}
}
v___jp_861_:
{
if (v___y_862_ == 0)
{
lean_object* v___x_863_; 
lean_inc(v_fst_856_);
v___x_863_ = l_Lean_executeReservedNameAction(v_fst_856_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; lean_object* v_env_865_; uint8_t v___x_866_; 
lean_dec_ref_known(v___x_863_, 1);
v___x_864_ = lean_st_ref_get(v___y_818_);
v_env_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref(v_env_865_);
lean_dec(v___x_864_);
v___x_866_ = l_Lean_Environment_containsOnBranch(v_env_865_, v_fst_856_);
lean_dec_ref(v_env_865_);
v_a_854_ = v___x_866_;
goto v___jp_853_;
}
else
{
lean_object* v_a_867_; uint8_t v___x_868_; 
lean_del_object(v___x_824_);
lean_dec(v_head_821_);
v_a_867_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_863_, 1);
v___x_868_ = l_Lean_Exception_isInterrupt(v_a_867_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
lean_inc(v_a_867_);
v___x_869_ = l_Lean_Exception_isRuntime(v_a_867_);
v___y_827_ = v_a_867_;
v___y_828_ = v___x_869_;
goto v___jp_826_;
}
else
{
v___y_827_ = v_a_867_;
v___y_828_ = v___x_868_;
goto v___jp_826_;
}
}
}
else
{
v_a_854_ = v___x_860_;
goto v___jp_853_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_814_ = stack[0].m_obj;
lean_object* v_x_815_ = stack[1].m_obj;
lean_object* v_x_816_ = stack[2].m_obj;
lean_object* v___y_817_ = stack[3].m_obj;
lean_object* v___y_818_ = stack[4].m_obj;
lean_object* v_res_874_;
v_res_874_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_814_, v_x_815_, v_x_816_, v___y_817_, v___y_818_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_875_, v_x_876_, v_x_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_box(0);
return v___x_883_;
}
else
{
lean_object* v_head_884_; lean_object* v_tail_885_; lean_object* v_fst_886_; uint8_t v___x_887_; 
v_head_884_ = lean_ctor_get(v_x_882_, 0);
v_tail_885_ = lean_ctor_get(v_x_882_, 1);
v_fst_886_ = lean_ctor_get(v_head_884_, 0);
v___x_887_ = l_Lean_isPrivateName(v_fst_886_);
if (v___x_887_ == 0)
{
v_x_882_ = v_tail_885_;
goto _start;
}
else
{
lean_object* v___x_889_; 
lean_inc(v_head_884_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_head_884_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_890_);
lean_dec(v_x_890_);
return v_res_891_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; 
v___x_896_ = 1;
v___x_897_ = 0;
v___x_898_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_892_, v___x_896_, v___x_897_, v___y_893_, v___y_894_);
return v___x_898_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_892_ = stack[0].m_obj;
lean_object* v___y_893_ = stack[1].m_obj;
lean_object* v___y_894_ = stack[2].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_892_, v___y_893_, v___y_894_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_904_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_906_);
v___x_909_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_908_, v_opt_905_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_box(v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_905_ = stack[0].m_obj;
lean_object* v___y_906_ = stack[1].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_905_, v___y_906_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_913_, v___y_914_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_opt_913_);
return v_res_916_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_env_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_950_; 
v___x_927_ = lean_st_ref_get(v___y_925_);
v_env_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc_ref(v_env_928_);
lean_dec(v___x_927_);
v___x_929_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_930_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_929_, v___y_924_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_950_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v_isExporting_940_; 
v_isExporting_940_ = lean_ctor_get_uint8(v_env_928_, sizeof(void*)*13);
lean_dec_ref(v_env_928_);
if (v_isExporting_940_ == 0)
{
lean_dec(v_a_931_);
lean_dec(v_id_923_);
goto v___jp_935_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_isPrivateName(v_id_923_);
if (v___x_941_ == 0)
{
lean_dec(v_a_931_);
lean_dec(v_id_923_);
goto v___jp_935_;
}
else
{
uint8_t v___x_942_; 
v___x_942_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
if (v___x_942_ == 0)
{
lean_dec(v_id_923_);
goto v___jp_935_;
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_933_);
v___x_943_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_944_ = 0;
v___x_945_ = l_Lean_MessageData_ofConstName(v_id_923_, v___x_944_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_943_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_948_, v___y_924_, v___y_925_);
return v___x_949_;
}
}
}
v___jp_935_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_923_ = stack[0].m_obj;
lean_object* v___y_924_ = stack[1].m_obj;
lean_object* v___y_925_ = stack[2].m_obj;
lean_object* v_res_951_;
v_res_951_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_956_;
}
}
lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_957_, uint8_t v_enableLog_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_toCold_963_; lean_object* v_env_964_; lean_object* v_currNamespace_965_; lean_object* v_openDecls_966_; lean_object* v___x_967_; lean_object* v_res_968_; lean_object* v___x_969_; 
v___x_962_ = lean_st_ref_get(v___y_960_);
v_toCold_963_ = lean_ctor_get(v___y_959_, 0);
v_env_964_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_962_);
v_currNamespace_965_ = lean_ctor_get(v_toCold_963_, 4);
v_openDecls_966_ = lean_ctor_get(v_toCold_963_, 5);
v___x_967_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_959_);
lean_inc(v_openDecls_966_);
lean_inc(v_currNamespace_965_);
v_res_968_ = l_Lean_ResolveName_resolveGlobalName(v_env_964_, v___x_967_, v_currNamespace_965_, v_openDecls_966_, v_id_957_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_st_ref_get(v___y_960_);
if (v_enableLog_958_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v___x_969_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_res_968_);
return v___x_970_;
}
else
{
lean_object* v_env_971_; uint8_t v_isExporting_972_; 
v_env_971_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_969_);
v_isExporting_972_ = lean_ctor_get_uint8(v_env_971_, sizeof(void*)*13);
lean_dec_ref(v_env_971_);
if (v_isExporting_972_ == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_res_968_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_968_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_975_; lean_object* v_fst_976_; lean_object* v___x_977_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v___x_974_, 1);
v_fst_976_ = lean_ctor_get(v_val_975_, 0);
lean_inc(v_fst_976_);
lean_dec(v_val_975_);
v___x_977_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_976_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_985_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v_res_968_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_res_968_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_res_968_);
v_a_986_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_977_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_977_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
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
else
{
lean_object* v___x_994_; 
lean_dec(v___x_974_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_res_968_);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_957_ = stack[0].m_obj;
uint8_t v_enableLog_958_ = stack[1].m_num;
lean_object* v___y_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_957_, v_enableLog_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_996_, lean_object* v_enableLog_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
uint8_t v_enableLog_boxed_1001_; lean_object* v_res_1002_; 
v_enableLog_boxed_1001_ = lean_unbox(v_enableLog_997_);
v_res_1002_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_996_, v_enableLog_boxed_1001_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1002_;
}
}
lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
uint8_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = 1;
lean_inc(v_id_1003_);
v___x_1008_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1003_, v___x_1007_, v_a_1004_, v_a_1005_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_box(0);
v___x_1011_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1003_, v_a_1009_, v___x_1010_, v_a_1004_, v_a_1005_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = l_List_reverse___redArg(v_a_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
return v___x_1011_;
}
}
else
{
lean_dec(v_id_1003_);
return v___x_1008_;
}
}
}
LEAN_EXPORT void l_Lean_realizeGlobalName_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1003_ = stack[0].m_obj;
lean_object* v_a_1004_ = stack[1].m_obj;
lean_object* v_a_1005_ = stack[2].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_realizeGlobalName(v_id_1003_, v_a_1004_, v_a_1005_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_realizeGlobalName(v_id_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1026_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1027_, v___y_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1027_ = stack[0].m_obj;
lean_object* v___y_1028_ = stack[1].m_obj;
lean_object* v___y_1029_ = stack[2].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1027_, v___y_1028_, v___y_1029_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_opt_1033_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = l_List_reverse___redArg(v_a_1039_);
return v___x_1040_;
}
else
{
lean_object* v_head_1041_; lean_object* v_tail_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v_head_1041_ = lean_ctor_get(v_a_1038_, 0);
v_tail_1042_ = lean_ctor_get(v_a_1038_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_1038_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1044_ = v_a_1038_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_tail_1042_);
lean_inc(v_head_1041_);
lean_dec(v_a_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; lean_object* v___x_1048_; 
v_fst_1046_ = lean_ctor_get(v_head_1041_, 0);
lean_inc(v_fst_1046_);
lean_dec(v_head_1041_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v_a_1039_);
lean_ctor_set(v___x_1044_, 0, v_fst_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_fst_1046_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_a_1039_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
v_a_1038_ = v_tail_1042_;
v_a_1039_ = v___x_1048_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_ref_1056_ = lean_ctor_get(v___y_1053_, 2);
v___x_1057_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1052_, v___y_1053_, v___y_1054_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_inc(v_ref_1056_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_ref_1056_);
lean_ctor_set(v___x_1062_, 1, v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1052_ = stack[0].m_obj;
lean_object* v___y_1053_ = stack[1].m_obj;
lean_object* v___y_1054_ = stack[2].m_obj;
lean_object* v_res_1067_;
v_res_1067_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1052_, v___y_1053_, v___y_1054_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1072_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1073_, lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_toCold_1078_; lean_object* v_currRecDepth_1079_; lean_object* v_ref_1080_; uint16_t v_optionFlags_1081_; uint8_t v_suppressElabErrors_1082_; uint8_t v_isRecordingDeps_1083_; lean_object* v_ref_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_toCold_1078_ = lean_ctor_get(v___y_1075_, 0);
v_currRecDepth_1079_ = lean_ctor_get(v___y_1075_, 1);
v_ref_1080_ = lean_ctor_get(v___y_1075_, 2);
v_optionFlags_1081_ = lean_ctor_get_uint16(v___y_1075_, sizeof(void*)*3);
v_suppressElabErrors_1082_ = lean_ctor_get_uint8(v___y_1075_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1083_ = lean_ctor_get_uint8(v___y_1075_, sizeof(void*)*3 + 3);
v_ref_1084_ = l_Lean_replaceRef(v_ref_1073_, v_ref_1080_);
lean_inc(v_currRecDepth_1079_);
lean_inc_ref(v_toCold_1078_);
v___x_1085_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1085_, 0, v_toCold_1078_);
lean_ctor_set(v___x_1085_, 1, v_currRecDepth_1079_);
lean_ctor_set(v___x_1085_, 2, v_ref_1084_);
lean_ctor_set_uint16(v___x_1085_, sizeof(void*)*3, v_optionFlags_1081_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3 + 2, v_suppressElabErrors_1082_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3 + 3, v_isRecordingDeps_1083_);
v___x_1086_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1074_, v___x_1085_, v___y_1076_);
lean_dec_ref_known(v___x_1085_, 3);
return v___x_1086_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1073_ = stack[0].m_obj;
lean_object* v_msg_1074_ = stack[1].m_obj;
lean_object* v___y_1075_ = stack[2].m_obj;
lean_object* v___y_1076_ = stack[3].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1073_, v_msg_1074_, v___y_1075_, v___y_1076_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1088_, v_msg_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v_ref_1088_);
return v_res_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1127_, lean_object* v_declHint_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_env_1133_; uint8_t v___x_1134_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_st_ref_get(v___y_1129_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = l_Lean_Name_isAnonymous(v_declHint_1128_);
if (v___x_1134_ == 0)
{
uint8_t v_isExporting_1135_; 
v_isExporting_1135_ = lean_ctor_get_uint8(v_env_1133_, sizeof(void*)*13);
if (v_isExporting_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec_ref(v_env_1133_);
lean_dec(v_declHint_1128_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_msg_1127_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
lean_inc_ref(v_env_1133_);
v___x_1137_ = l_Lean_Environment_setExporting(v_env_1133_, v___x_1134_);
lean_inc(v_declHint_1128_);
lean_inc_ref(v___x_1137_);
v___x_1138_ = l_Lean_Environment_contains(v___x_1137_, v_declHint_1128_, v_isExporting_1135_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v___x_1137_);
lean_dec_ref(v_env_1133_);
lean_dec(v_declHint_1128_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_msg_1127_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_c_1145_; lean_object* v___x_1146_; 
v___x_1140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1142_ = l_Lean_Options_empty;
v___x_1143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1137_);
lean_ctor_set(v___x_1143_, 1, v___x_1140_);
lean_ctor_set(v___x_1143_, 2, v___x_1141_);
lean_ctor_set(v___x_1143_, 3, v___x_1142_);
lean_inc(v_declHint_1128_);
v___x_1144_ = l_Lean_MessageData_ofConstName(v_declHint_1128_, v___x_1134_);
v_c_1145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1145_, 0, v___x_1143_);
lean_ctor_set(v_c_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1133_, v_declHint_1128_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec_ref(v_env_1133_);
lean_dec(v_declHint_1128_);
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v_c_1145_);
v___x_1149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_note(v___x_1150_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_msg_1127_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1210_; 
v_val_1154_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1156_ = v___x_1146_;
v_isShared_1157_ = v_isSharedCheck_1210_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_val_1154_);
lean_dec(v___x_1146_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1210_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v_modules_1159_; lean_object* v_moduleNames_1160_; lean_object* v_mod_1161_; uint8_t v___y_1163_; uint8_t v___x_1193_; 
v___x_1158_ = l_Lean_Environment_header(v_env_1133_);
lean_dec_ref(v_env_1133_);
v_modules_1159_ = lean_ctor_get(v___x_1158_, 3);
lean_inc_ref(v_modules_1159_);
v_moduleNames_1160_ = lean_ctor_get(v___x_1158_, 4);
lean_inc_ref(v_moduleNames_1160_);
lean_dec_ref(v___x_1158_);
v_mod_1161_ = lean_array_get(v___x_1131_, v_moduleNames_1160_, v_val_1154_);
lean_dec_ref(v_moduleNames_1160_);
v___x_1193_ = l_Lean_isPrivateName(v_declHint_1128_);
lean_dec(v_declHint_1128_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_array_get_size(v_modules_1159_);
v___x_1195_ = lean_nat_dec_lt(v_val_1154_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_dec_ref(v_modules_1159_);
lean_dec(v_val_1154_);
v___y_1163_ = v___x_1193_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1196_; lean_object* v_toImport_1197_; uint8_t v_isExported_1198_; 
v___x_1196_ = lean_array_fget(v_modules_1159_, v_val_1154_);
lean_dec(v_val_1154_);
lean_dec_ref(v_modules_1159_);
v_toImport_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_toImport_1197_);
lean_dec(v___x_1196_);
v_isExported_1198_ = lean_ctor_get_uint8(v_toImport_1197_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1197_);
v___y_1163_ = v_isExported_1198_;
goto v___jp_1162_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_modules_1159_);
lean_del_object(v___x_1156_);
lean_dec(v_val_1154_);
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_c_1145_);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_Lean_MessageData_ofName(v_mod_1161_);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_MessageData_note(v___x_1206_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_msg_1127_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
v___jp_1162_:
{
if (v___y_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_c_1145_);
v___x_1166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_ofName(v_mod_1161_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_MessageData_note(v___x_1171_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_msg_1127_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1173_);
v___x_1175_ = v___x_1156_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_c_1145_);
v___x_1179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_MessageData_ofName(v_mod_1161_);
lean_inc_ref(v___x_1181_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1181_);
v___x_1186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_MessageData_note(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_msg_1127_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1189_);
v___x_1191_ = v___x_1156_;
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
}
}
}
}
}
}
else
{
lean_object* v___x_1211_; 
lean_dec_ref(v_env_1133_);
lean_dec(v_declHint_1128_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_msg_1127_);
return v___x_1211_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1127_ = stack[0].m_obj;
lean_object* v_declHint_1128_ = stack[1].m_obj;
lean_object* v___y_1129_ = stack[2].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1127_, v_declHint_1128_, v___y_1129_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1213_, lean_object* v_declHint_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1213_, v_declHint_1214_, v___y_1215_);
lean_dec(v___y_1215_);
return v_res_1217_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1218_, lean_object* v_declHint_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1233_; 
v___x_1223_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1218_, v_declHint_1219_, v___y_1221_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1228_ = l_Lean_unknownIdentifierMessageTag;
v___x_1229_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_a_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1218_ = stack[0].m_obj;
lean_object* v_declHint_1219_ = stack[1].m_obj;
lean_object* v___y_1220_ = stack[2].m_obj;
lean_object* v___y_1221_ = stack[3].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1218_, v_declHint_1219_, v___y_1220_, v___y_1221_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1235_, lean_object* v_declHint_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1235_, v_declHint_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1240_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1241_, lean_object* v_msg_1242_, lean_object* v_declHint_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v_a_1248_; lean_object* v___x_1249_; 
v___x_1247_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1242_, v_declHint_1243_, v___y_1244_, v___y_1245_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1241_, v_a_1248_, v___y_1244_, v___y_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1241_ = stack[0].m_obj;
lean_object* v_msg_1242_ = stack[1].m_obj;
lean_object* v_declHint_1243_ = stack[2].m_obj;
lean_object* v___y_1244_ = stack[3].m_obj;
lean_object* v___y_1245_ = stack[4].m_obj;
lean_object* v_res_1250_;
v_res_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1241_, v_msg_1242_, v_declHint_1243_, v___y_1244_, v___y_1245_);
stack->m_obj
 = v_res_1250_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1251_, lean_object* v_msg_1252_, lean_object* v_declHint_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1251_, v_msg_1252_, v_declHint_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v_ref_1251_);
return v_res_1257_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1264_, lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1269_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1270_ = 0;
lean_inc(v_constName_1265_);
v___x_1271_ = l_Lean_MessageData_ofConstName(v_constName_1265_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1264_, v___x_1274_, v_constName_1265_, v___y_1266_, v___y_1267_);
return v___x_1275_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1264_ = stack[0].m_obj;
lean_object* v_constName_1265_ = stack[1].m_obj;
lean_object* v___y_1266_ = stack[2].m_obj;
lean_object* v___y_1267_ = stack[3].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1264_, v_constName_1265_, v___y_1266_, v___y_1267_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1277_, lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1277_, v_constName_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v_ref_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
if (lean_obj_tag(v_a_1283_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_reverse___redArg(v_a_1284_);
return v___x_1285_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1298_; 
v_head_1286_ = lean_ctor_get(v_a_1283_, 0);
v_tail_1287_ = lean_ctor_get(v_a_1283_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1289_ = v_a_1283_;
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_head_1286_);
lean_dec(v_a_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_snd_1291_; uint8_t v___x_1292_; 
v_snd_1291_ = lean_ctor_get(v_head_1286_, 1);
v___x_1292_ = l_List_isEmpty___redArg(v_snd_1291_);
if (v___x_1292_ == 0)
{
lean_del_object(v___x_1289_);
lean_dec(v_head_1286_);
v_a_1283_ = v_tail_1287_;
goto _start;
}
else
{
lean_object* v___x_1295_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_a_1284_);
v___x_1295_ = v___x_1289_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_head_1286_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1284_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v_a_1283_ = v_tail_1287_;
v_a_1284_ = v___x_1295_;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1299_, lean_object* v_cs_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v_cs_1305_; uint8_t v___x_1309_; 
v___x_1304_ = lean_box(0);
v_cs_1305_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1300_, v___x_1304_);
v___x_1309_ = l_List_isEmpty___redArg(v_cs_1305_);
if (v___x_1309_ == 0)
{
lean_dec(v_n_1299_);
goto v___jp_1306_;
}
else
{
lean_object* v_ref_1310_; lean_object* v___x_1311_; lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_cs_1305_);
v_ref_1310_ = lean_ctor_get(v___y_1301_, 2);
v___x_1311_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1310_, v_n_1299_, v___y_1301_, v___y_1302_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1305_, v___x_1304_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
LEAN_EXPORT void l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1299_ = stack[0].m_obj;
lean_object* v_cs_1300_ = stack[1].m_obj;
lean_object* v___y_1301_ = stack[2].m_obj;
lean_object* v___y_1302_ = stack[3].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1299_, v_cs_1300_, v___y_1301_, v___y_1302_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1321_, lean_object* v_cs_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1321_, v_cs_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1326_;
}
}
lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1331_; 
lean_inc(v_n_1327_);
v___x_1331_ = l_Lean_realizeGlobalName(v_n_1327_, v_a_1328_, v_a_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1333_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1333_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1327_, v_a_1332_, v_a_1328_, v_a_1329_);
return v___x_1333_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_n_1327_);
v_a_1334_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1331_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_realizeGlobalConstCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1327_ = stack[0].m_obj;
lean_object* v_a_1328_ = stack[1].m_obj;
lean_object* v_a_1329_ = stack[2].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_realizeGlobalConstCore(v_n_1327_, v_a_1328_, v_a_1329_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_realizeGlobalConstCore(v_n_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
return v_res_1347_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1348_, lean_object* v_ref_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1349_, v_constName_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1349_ = stack[1].m_obj;
lean_object* v_constName_1350_ = stack[2].m_obj;
lean_object* v___y_1351_ = stack[3].m_obj;
lean_object* v___y_1352_ = stack[4].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_box(0), v_ref_1349_, v_constName_1350_, v___y_1351_, v___y_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_ref_1357_, lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1356_, v_ref_1357_, v_constName_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_ref_1357_);
return v_res_1362_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1363_, lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v_declHint_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1364_, v_msg_1365_, v_declHint_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1364_ = stack[1].m_obj;
lean_object* v_msg_1365_ = stack[2].m_obj;
lean_object* v_declHint_1366_ = stack[3].m_obj;
lean_object* v___y_1367_ = stack[4].m_obj;
lean_object* v___y_1368_ = stack[5].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_box(0), v_ref_1364_, v_msg_1365_, v_declHint_1366_, v___y_1367_, v___y_1368_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_ref_1373_, lean_object* v_msg_1374_, lean_object* v_declHint_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1372_, v_ref_1373_, v_msg_1374_, v_declHint_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v_ref_1373_);
return v_res_1379_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1380_, lean_object* v_declHint_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1380_, v_declHint_1381_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1380_ = stack[0].m_obj;
lean_object* v_declHint_1381_ = stack[1].m_obj;
lean_object* v___y_1382_ = stack[2].m_obj;
lean_object* v___y_1383_ = stack[3].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1380_, v_declHint_1381_, v___y_1382_, v___y_1383_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1387_, v_declHint_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1392_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1393_, lean_object* v_ref_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1394_, v_msg_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1394_ = stack[1].m_obj;
lean_object* v_msg_1395_ = stack[2].m_obj;
lean_object* v___y_1396_ = stack[3].m_obj;
lean_object* v___y_1397_ = stack[4].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_box(0), v_ref_1394_, v_msg_1395_, v___y_1396_, v___y_1397_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_ref_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1401_, v_ref_1402_, v_msg_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_ref_1402_);
return v_res_1407_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1409_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1409_ = stack[1].m_obj;
lean_object* v___y_1410_ = stack[2].m_obj;
lean_object* v___y_1411_ = stack[3].m_obj;
lean_object* v_res_1414_;
v_res_1414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_box(0), v_msg_1409_, v___y_1410_, v___y_1411_);
stack->m_obj
 = v_res_1414_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1415_, v_msg_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
if (lean_obj_tag(v_a_1421_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = l_List_reverse___redArg(v_a_1422_);
return v___x_1423_;
}
else
{
lean_object* v_head_1424_; lean_object* v_tail_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1434_; 
v_head_1424_ = lean_ctor_get(v_a_1421_, 0);
v_tail_1425_ = lean_ctor_get(v_a_1421_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_a_1421_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1427_ = v_a_1421_;
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_tail_1425_);
lean_inc(v_head_1424_);
lean_dec(v_a_1421_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = l_Lean_MessageData_ofExpr(v_head_1424_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_a_1422_);
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_a_1422_);
v___x_1431_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
v_a_1421_ = v_tail_1425_;
v_a_1422_ = v___x_1431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
if (lean_obj_tag(v_a_1435_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = l_List_reverse___redArg(v_a_1436_);
return v___x_1437_;
}
else
{
lean_object* v_head_1438_; lean_object* v_tail_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1449_; 
v_head_1438_ = lean_ctor_get(v_a_1435_, 0);
v_tail_1439_ = lean_ctor_get(v_a_1435_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_a_1435_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1441_ = v_a_1435_;
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_tail_1439_);
lean_inc(v_head_1438_);
lean_dec(v_a_1435_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Lean_mkConst(v_head_1438_, v___x_1443_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v_a_1436_);
lean_ctor_set(v___x_1441_, 0, v___x_1444_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_a_1436_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v_a_1435_ = v_tail_1439_;
v_a_1436_ = v___x_1446_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1456_, lean_object* v_cs_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
if (lean_obj_tag(v_cs_1457_) == 1)
{
lean_object* v_tail_1473_; 
v_tail_1473_ = lean_ctor_get(v_cs_1457_, 1);
if (lean_obj_tag(v_tail_1473_) == 0)
{
lean_object* v_head_1474_; lean_object* v___x_1475_; 
lean_dec(v_n_1456_);
v_head_1474_ = lean_ctor_get(v_cs_1457_, 0);
lean_inc(v_head_1474_);
lean_dec_ref_known(v_cs_1457_, 2);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_head_1474_);
return v___x_1475_;
}
else
{
goto v___jp_1461_;
}
}
else
{
goto v___jp_1461_;
}
v___jp_1461_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1462_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1463_ = l_Lean_MessageData_ofName(v_n_1456_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1457_, v___x_1467_);
v___x_1469_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1468_, v___x_1467_);
v___x_1470_ = l_Lean_MessageData_ofList(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1466_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1471_, v___y_1458_, v___y_1459_);
return v___x_1472_;
}
}
}
LEAN_EXPORT void l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1456_ = stack[0].m_obj;
lean_object* v_cs_1457_ = stack[1].m_obj;
lean_object* v___y_1458_ = stack[2].m_obj;
lean_object* v___y_1459_ = stack[3].m_obj;
lean_object* v_res_1476_;
v_res_1476_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1456_, v_cs_1457_, v___y_1458_, v___y_1459_);
stack->m_obj
 = v_res_1476_;
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1477_, lean_object* v_cs_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1477_, v_cs_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1482_;
}
}
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1487_; 
lean_inc(v_n_1483_);
v___x_1487_ = l_Lean_realizeGlobalConstCore(v_n_1483_, v_a_1484_, v_a_1485_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1483_, v_a_1488_, v_a_1484_, v_a_1485_);
return v___x_1489_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_n_1483_);
v_a_1490_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1487_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_realizeGlobalConstNoOverloadCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1483_ = stack[0].m_obj;
lean_object* v_a_1484_ = stack[1].m_obj;
lean_object* v_a_1485_ = stack[2].m_obj;
lean_object* v_res_1498_;
v_res_1498_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1483_, v_a_1484_, v_a_1485_);
stack->m_obj
 = v_res_1498_;
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
if (lean_obj_tag(v_a_1504_) == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_array_to_list(v_a_1505_);
return v___x_1506_;
}
else
{
lean_object* v_head_1507_; 
v_head_1507_ = lean_ctor_get(v_a_1504_, 0);
if (lean_obj_tag(v_head_1507_) == 1)
{
lean_object* v_fields_1508_; 
v_fields_1508_ = lean_ctor_get(v_head_1507_, 1);
if (lean_obj_tag(v_fields_1508_) == 0)
{
lean_object* v_tail_1509_; lean_object* v_n_1510_; lean_object* v___x_1511_; 
lean_inc_ref(v_head_1507_);
v_tail_1509_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_tail_1509_);
lean_dec_ref_known(v_a_1504_, 2);
v_n_1510_ = lean_ctor_get(v_head_1507_, 0);
lean_inc(v_n_1510_);
lean_dec_ref_known(v_head_1507_, 2);
v___x_1511_ = lean_array_push(v_a_1505_, v_n_1510_);
v_a_1504_ = v_tail_1509_;
v_a_1505_ = v___x_1511_;
goto _start;
}
else
{
lean_object* v_tail_1513_; 
v_tail_1513_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_tail_1513_);
lean_dec_ref_known(v_a_1504_, 2);
v_a_1504_ = v_tail_1513_;
goto _start;
}
}
else
{
lean_object* v_tail_1515_; 
v_tail_1515_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_tail_1515_);
lean_dec_ref_known(v_a_1504_, 2);
v_a_1504_ = v_tail_1515_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1523_ = l_Lean_MessageData_ofFormat(v___x_1522_);
return v___x_1523_;
}
}
lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1524_, lean_object* v_k_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
if (lean_obj_tag(v_stx_1524_) == 3)
{
lean_object* v_val_1529_; lean_object* v_preresolved_1530_; lean_object* v___x_1531_; lean_object* v_pre_1532_; uint8_t v___x_1533_; 
v_val_1529_ = lean_ctor_get(v_stx_1524_, 2);
lean_inc(v_val_1529_);
v_preresolved_1530_ = lean_ctor_get(v_stx_1524_, 3);
v___x_1531_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1530_);
v_pre_1532_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1530_, v___x_1531_);
v___x_1533_ = l_List_isEmpty___redArg(v_pre_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec_ref_known(v_stx_1524_, 4);
lean_dec(v_val_1529_);
lean_dec_ref(v_k_1525_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_pre_1532_);
return v___x_1534_;
}
else
{
lean_object* v_toCold_1535_; lean_object* v_currRecDepth_1536_; lean_object* v_ref_1537_; uint16_t v_optionFlags_1538_; uint8_t v_suppressElabErrors_1539_; uint8_t v_isRecordingDeps_1540_; lean_object* v_ref_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_pre_1532_);
v_toCold_1535_ = lean_ctor_get(v___y_1526_, 0);
v_currRecDepth_1536_ = lean_ctor_get(v___y_1526_, 1);
v_ref_1537_ = lean_ctor_get(v___y_1526_, 2);
v_optionFlags_1538_ = lean_ctor_get_uint16(v___y_1526_, sizeof(void*)*3);
v_suppressElabErrors_1539_ = lean_ctor_get_uint8(v___y_1526_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1540_ = lean_ctor_get_uint8(v___y_1526_, sizeof(void*)*3 + 3);
v_ref_1541_ = l_Lean_replaceRef(v_stx_1524_, v_ref_1537_);
lean_dec_ref_known(v_stx_1524_, 4);
lean_inc(v_currRecDepth_1536_);
lean_inc_ref(v_toCold_1535_);
v___x_1542_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1542_, 0, v_toCold_1535_);
lean_ctor_set(v___x_1542_, 1, v_currRecDepth_1536_);
lean_ctor_set(v___x_1542_, 2, v_ref_1541_);
lean_ctor_set_uint16(v___x_1542_, sizeof(void*)*3, v_optionFlags_1538_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 2, v_suppressElabErrors_1539_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 3, v_isRecordingDeps_1540_);
lean_inc(v___y_1527_);
v___x_1543_ = lean_apply_4(v_k_1525_, v_val_1529_, v___x_1542_, v___y_1527_, lean_box(0));
return v___x_1543_;
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v_k_1525_);
v___x_1544_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1545_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1524_, v___x_1544_, v___y_1526_, v___y_1527_);
lean_dec(v_stx_1524_);
return v___x_1545_;
}
}
}
LEAN_EXPORT void l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1524_ = stack[0].m_obj;
lean_object* v_k_1525_ = stack[1].m_obj;
lean_object* v___y_1526_ = stack[2].m_obj;
lean_object* v___y_1527_ = stack[3].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1524_, v_k_1525_, v___y_1526_, v___y_1527_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1547_, lean_object* v_k_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1547_, v_k_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1552_;
}
}
lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_toCold_1558_; lean_object* v_currRecDepth_1559_; lean_object* v_ref_1560_; uint16_t v_optionFlags_1561_; uint8_t v_suppressElabErrors_1562_; uint8_t v_isRecordingDeps_1563_; lean_object* v___x_1564_; lean_object* v_ref_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_toCold_1558_ = lean_ctor_get(v_a_1555_, 0);
v_currRecDepth_1559_ = lean_ctor_get(v_a_1555_, 1);
v_ref_1560_ = lean_ctor_get(v_a_1555_, 2);
v_optionFlags_1561_ = lean_ctor_get_uint16(v_a_1555_, sizeof(void*)*3);
v_suppressElabErrors_1562_ = lean_ctor_get_uint8(v_a_1555_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1563_ = lean_ctor_get_uint8(v_a_1555_, sizeof(void*)*3 + 3);
v___x_1564_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1565_ = l_Lean_replaceRef(v_stx_1554_, v_ref_1560_);
lean_inc(v_currRecDepth_1559_);
lean_inc_ref(v_toCold_1558_);
v___x_1566_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1566_, 0, v_toCold_1558_);
lean_ctor_set(v___x_1566_, 1, v_currRecDepth_1559_);
lean_ctor_set(v___x_1566_, 2, v_ref_1565_);
lean_ctor_set_uint16(v___x_1566_, sizeof(void*)*3, v_optionFlags_1561_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*3 + 2, v_suppressElabErrors_1562_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*3 + 3, v_isRecordingDeps_1563_);
v___x_1567_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1554_, v___x_1564_, v___x_1566_, v_a_1556_);
lean_dec_ref_known(v___x_1566_, 3);
return v___x_1567_;
}
}
LEAN_EXPORT void l_Lean_realizeGlobalConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1554_ = stack[0].m_obj;
lean_object* v_a_1555_ = stack[1].m_obj;
lean_object* v_a_1556_ = stack[2].m_obj;
lean_object* v_res_1568_;
v_res_1568_ = l_Lean_realizeGlobalConst(v_stx_1554_, v_a_1555_, v_a_1556_);
stack->m_obj
 = v_res_1568_;
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_realizeGlobalConst(v_stx_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
return v_res_1573_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_instMonadEIO___redArg();
return v___x_1574_;
}
}
lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_toApplicative_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1614_; 
v___x_1581_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1582_ = l_StateRefT_x27_instMonad___redArg(v___x_1581_);
v_toApplicative_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1582_, 1);
lean_dec(v_unused_1615_);
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1614_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_toApplicative_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1614_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_toFunctor_1587_; lean_object* v_toSeq_1588_; lean_object* v_toSeqLeft_1589_; lean_object* v_toSeqRight_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1612_; 
v_toFunctor_1587_ = lean_ctor_get(v_toApplicative_1583_, 0);
v_toSeq_1588_ = lean_ctor_get(v_toApplicative_1583_, 2);
v_toSeqLeft_1589_ = lean_ctor_get(v_toApplicative_1583_, 3);
v_toSeqRight_1590_ = lean_ctor_get(v_toApplicative_1583_, 4);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_toApplicative_1583_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_toApplicative_1583_, 1);
lean_dec(v_unused_1613_);
v___x_1592_ = v_toApplicative_1583_;
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_toSeqRight_1590_);
lean_inc(v_toSeqLeft_1589_);
lean_inc(v_toSeq_1588_);
lean_inc(v_toFunctor_1587_);
lean_dec(v_toApplicative_1583_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___x_1603_; 
v___f_1594_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1595_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1587_);
v___f_1596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1596_, 0, v_toFunctor_1587_);
v___f_1597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1597_, 0, v_toFunctor_1587_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___f_1596_);
lean_ctor_set(v___x_1598_, 1, v___f_1597_);
v___f_1599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1599_, 0, v_toSeqRight_1590_);
v___f_1600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1600_, 0, v_toSeqLeft_1589_);
v___f_1601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1601_, 0, v_toSeq_1588_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 4, v___f_1599_);
lean_ctor_set(v___x_1592_, 3, v___f_1600_);
lean_ctor_set(v___x_1592_, 2, v___f_1601_);
lean_ctor_set(v___x_1592_, 1, v___f_1594_);
lean_ctor_set(v___x_1592_, 0, v___x_1598_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___f_1594_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v___f_1601_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v___f_1600_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v___f_1599_);
v___x_1603_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1605_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___f_1595_);
lean_ctor_set(v___x_1585_, 0, v___x_1603_);
v___x_1605_ = v___x_1585_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___f_1595_);
v___x_1605_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_195__overap_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = l_instInhabitedOfMonad___redArg(v___x_1605_, v___x_1606_);
v___x_195__overap_1608_ = lean_panic_fn_borrowed(v___x_1607_, v_msg_1577_);
lean_dec(v___x_1607_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1609_ = lean_apply_3(v___x_195__overap_1608_, v___y_1578_, v___y_1579_, lean_box(0));
return v___x_1609_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1577_ = stack[0].m_obj;
lean_object* v___y_1578_ = stack[1].m_obj;
lean_object* v___y_1579_ = stack[2].m_obj;
lean_object* v_res_1616_;
v_res_1616_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1577_, v___y_1578_, v___y_1579_);
stack->m_obj
 = v_res_1616_;
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
lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1667_, lean_object* v_cs_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
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
lean_dec_ref_known(v_cs_1668_, 2);
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
LEAN_EXPORT void l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1667_ = stack[0].m_obj;
lean_object* v_cs_1668_ = stack[1].m_obj;
lean_object* v___y_1669_ = stack[2].m_obj;
lean_object* v___y_1670_ = stack[3].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1667_, v_cs_1668_, v___y_1669_, v___y_1670_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1695_, lean_object* v_cs_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1695_, v_cs_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1700_;
}
}
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
lean_inc(v_id_1701_);
v___x_1705_ = l_Lean_realizeGlobalConst(v_id_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1701_, v_a_1706_, v_a_1702_, v_a_1703_);
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_id_1701_);
v_a_1708_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1705_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_realizeGlobalConstNoOverload_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1701_ = stack[0].m_obj;
lean_object* v_a_1702_ = stack[1].m_obj;
lean_object* v_a_1703_ = stack[2].m_obj;
lean_object* v_res_1716_;
v_res_1716_ = l_Lean_realizeGlobalConstNoOverload(v_id_1701_, v_a_1702_, v_a_1703_);
stack->m_obj
 = v_res_1716_;
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_realizeGlobalConstNoOverload(v_id_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1721_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(3863082579u);
v___x_1754_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1755_ = l_Lean_Name_num___override(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1758_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1759_ = l_Lean_Name_str___override(v___x_1758_, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1762_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1763_ = l_Lean_Name_str___override(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_unsigned_to_nat(2u);
v___x_1765_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1766_ = l_Lean_Name_num___override(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1769_ = 0;
v___x_1770_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1771_ = l_Lean_registerTraceClass(v___x_1768_, v___x_1769_, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT void l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1772_;
v_res_1772_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1774_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
uint8_t v___x_14_; 
v___x_14_ = l_Lean_initializing();
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec_ref(v_act_12_);
v___x_15_ = lean_obj_once(&l_Lean_registerReservedNameAction___closed__1, &l_Lean_registerReservedNameAction___closed__1_once, _init_l_Lean_registerReservedNameAction___closed__1);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_17_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_18_ = lean_st_ref_take(v___x_17_);
v___x_19_ = lean_array_push(v___x_18_, v_act_12_);
v___x_20_ = lean_st_ref_put(v___x_17_, v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNameAction___boxed(lean_object* v_act_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_registerReservedNameAction(v_act_22_);
return v_res_24_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_unsigned_to_nat(32u);
v___x_26_ = lean_mk_empty_array_with_capacity(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_28_ = ((size_t)5ULL);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_unsigned_to_nat(32u);
v___x_31_ = lean_mk_empty_array_with_capacity(v___x_30_);
v___x_32_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0);
v___x_33_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_29_);
lean_ctor_set(v___x_33_, 3, v___x_29_);
lean_ctor_set_usize(v___x_33_, 4, v___x_28_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; lean_object* v_traceState_37_; lean_object* v_traces_38_; lean_object* v___x_39_; lean_object* v_traceState_40_; lean_object* v_env_41_; lean_object* v_nextMacroScope_42_; lean_object* v_ngen_43_; lean_object* v_auxDeclNGen_44_; lean_object* v_cache_45_; lean_object* v_recordedDeps_46_; lean_object* v_messages_47_; lean_object* v_infoState_48_; lean_object* v_snapshotTasks_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_68_; 
v___x_36_ = lean_st_ref_get(v___y_34_);
v_traceState_37_ = lean_ctor_get(v___x_36_, 4);
lean_inc_ref(v_traceState_37_);
lean_dec(v___x_36_);
v_traces_38_ = lean_ctor_get(v_traceState_37_, 0);
lean_inc_ref(v_traces_38_);
lean_dec_ref(v_traceState_37_);
v___x_39_ = lean_st_ref_take(v___y_34_);
v_traceState_40_ = lean_ctor_get(v___x_39_, 4);
v_env_41_ = lean_ctor_get(v___x_39_, 0);
v_nextMacroScope_42_ = lean_ctor_get(v___x_39_, 1);
v_ngen_43_ = lean_ctor_get(v___x_39_, 2);
v_auxDeclNGen_44_ = lean_ctor_get(v___x_39_, 3);
v_cache_45_ = lean_ctor_get(v___x_39_, 5);
v_recordedDeps_46_ = lean_ctor_get(v___x_39_, 6);
v_messages_47_ = lean_ctor_get(v___x_39_, 7);
v_infoState_48_ = lean_ctor_get(v___x_39_, 8);
v_snapshotTasks_49_ = lean_ctor_get(v___x_39_, 9);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_68_ == 0)
{
v___x_51_ = v___x_39_;
v_isShared_52_ = v_isSharedCheck_68_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_snapshotTasks_49_);
lean_inc(v_infoState_48_);
lean_inc(v_messages_47_);
lean_inc(v_recordedDeps_46_);
lean_inc(v_cache_45_);
lean_inc(v_traceState_40_);
lean_inc(v_auxDeclNGen_44_);
lean_inc(v_ngen_43_);
lean_inc(v_nextMacroScope_42_);
lean_inc(v_env_41_);
lean_dec(v___x_39_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_68_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint64_t v_tid_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_66_; 
v_tid_53_ = lean_ctor_get_uint64(v_traceState_40_, sizeof(void*)*1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_traceState_40_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v_traceState_40_, 0);
lean_dec(v_unused_67_);
v___x_55_ = v_traceState_40_;
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
else
{
lean_dec(v_traceState_40_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_66_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_57_);
lean_ctor_set_uint64(v_reuseFailAlloc_65_, sizeof(void*)*1, v_tid_53_);
v___x_59_ = v_reuseFailAlloc_65_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_61_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 4, v___x_59_);
v___x_61_ = v___x_51_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_env_41_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_nextMacroScope_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_ngen_43_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_auxDeclNGen_44_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_cache_45_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v_recordedDeps_46_);
lean_ctor_set(v_reuseFailAlloc_64_, 7, v_messages_47_);
lean_ctor_set(v_reuseFailAlloc_64_, 8, v_infoState_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 9, v_snapshotTasks_49_);
v___x_61_ = v_reuseFailAlloc_64_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_st_ref_put(v___y_34_, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_traces_38_);
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_69_);
lean_dec(v___y_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(lean_object* v_opts_80_, lean_object* v_opt_81_){
_start:
{
lean_object* v_name_82_; lean_object* v_defValue_83_; lean_object* v_map_84_; lean_object* v___x_85_; 
v_name_82_ = lean_ctor_get(v_opt_81_, 0);
v_defValue_83_ = lean_ctor_get(v_opt_81_, 1);
v_map_84_ = lean_ctor_get(v_opts_80_, 0);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_84_, v_name_82_);
if (lean_obj_tag(v___x_85_) == 0)
{
uint8_t v___x_86_; 
v___x_86_ = lean_unbox(v_defValue_83_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; 
v_val_87_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v___x_85_, 1);
if (lean_obj_tag(v_val_87_) == 1)
{
uint8_t v_v_88_; 
v_v_88_ = lean_ctor_get_uint8(v_val_87_, 0);
lean_dec_ref_known(v_val_87_, 0);
return v_v_88_;
}
else
{
uint8_t v___x_89_; 
lean_dec(v_val_87_);
v___x_89_ = lean_unbox(v_defValue_83_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v_opts_90_, lean_object* v_opt_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_90_, v_opt_91_);
lean_dec_ref(v_opt_91_);
lean_dec_ref(v_opts_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_executeReservedNameAction___lam__0___closed__0));
v___x_96_ = l_Lean_stringToMessageData(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object* v_name_97_, lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_obj_once(&l_Lean_executeReservedNameAction___lam__0___closed__1, &l_Lean_executeReservedNameAction___lam__0___closed__1_once, _init_l_Lean_executeReservedNameAction___lam__0___closed__1);
v___x_103_ = l_Lean_MessageData_ofName(v_name_97_);
v___x_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object* v_name_106_, lean_object* v_x_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_executeReservedNameAction___lam__0(v_name_106_, v_x_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec_ref(v_x_107_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(lean_object* v_opts_112_, lean_object* v_opt_113_){
_start:
{
lean_object* v_name_114_; lean_object* v_defValue_115_; lean_object* v_map_116_; lean_object* v___x_117_; 
v_name_114_ = lean_ctor_get(v_opt_113_, 0);
v_defValue_115_ = lean_ctor_get(v_opt_113_, 1);
v_map_116_ = lean_ctor_get(v_opts_112_, 0);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_116_, v_name_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_inc(v_defValue_115_);
return v_defValue_115_;
}
else
{
lean_object* v_val_118_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_117_, 1);
if (lean_obj_tag(v_val_118_) == 3)
{
lean_object* v_v_119_; 
v_v_119_ = lean_ctor_get(v_val_118_, 0);
lean_inc(v_v_119_);
lean_dec_ref_known(v_val_118_, 1);
return v_v_119_;
}
else
{
lean_dec(v_val_118_);
lean_inc(v_defValue_115_);
return v_defValue_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(lean_object* v_opts_120_, lean_object* v_opt_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_120_, v_opt_121_);
lean_dec_ref(v_opt_121_);
lean_dec_ref(v_opts_120_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
lean_ctor_set(v___x_129_, 3, v___x_128_);
lean_ctor_set(v___x_129_, 4, v___x_127_);
lean_ctor_set(v___x_129_, 5, v___x_127_);
lean_ctor_set(v___x_129_, 6, v___x_127_);
lean_ctor_set(v___x_129_, 7, v___x_127_);
lean_ctor_set(v___x_129_, 8, v___x_127_);
lean_ctor_set(v___x_129_, 9, v___x_127_);
lean_ctor_set(v___x_129_, 10, v___x_127_);
lean_ctor_set(v___x_129_, 11, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_unsigned_to_nat(32u);
v___x_131_ = lean_mk_empty_array_with_capacity(v___x_130_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4(void){
_start:
{
size_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_133_ = ((size_t)5ULL);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_unsigned_to_nat(32u);
v___x_136_ = lean_mk_empty_array_with_capacity(v___x_135_);
v___x_137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3);
v___x_138_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_134_);
lean_ctor_set(v___x_138_, 3, v___x_134_);
lean_ctor_set_usize(v___x_138_, 4, v___x_133_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = lean_box(1);
v___x_140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4);
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
lean_ctor_set(v___x_142_, 2, v___x_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; lean_object* v_toCold_148_; lean_object* v_env_149_; lean_object* v_options_150_; uint8_t v___x_151_; lean_object* v_env_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_147_ = lean_st_ref_get(v___y_145_);
v_toCold_148_ = lean_ctor_get(v___y_144_, 0);
v_env_149_ = lean_ctor_get(v___x_147_, 0);
lean_inc_ref(v_env_149_);
lean_dec(v___x_147_);
v_options_150_ = lean_ctor_get(v_toCold_148_, 2);
v___x_151_ = 0;
v_env_152_ = l_Lean_Environment_setRecordingDeps(v_env_149_, v___x_151_);
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_150_);
v___x_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_155_, 0, v_env_152_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
lean_ctor_set(v___x_155_, 3, v_options_150_);
v___x_156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_msgData_143_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object* v_msgData_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t v_sz_163_, size_t v_i_164_, lean_object* v_bs_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_lt(v_i_164_, v_sz_163_);
if (v___x_166_ == 0)
{
return v_bs_165_;
}
else
{
lean_object* v_v_167_; lean_object* v_msg_168_; lean_object* v___x_169_; lean_object* v_bs_x27_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
v_v_167_ = lean_array_uget_borrowed(v_bs_165_, v_i_164_);
v_msg_168_ = lean_ctor_get(v_v_167_, 1);
lean_inc_ref(v_msg_168_);
v___x_169_ = lean_unsigned_to_nat(0u);
v_bs_x27_170_ = lean_array_uset(v_bs_165_, v_i_164_, v___x_169_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_i_164_, v___x_171_);
v___x_173_ = lean_array_uset(v_bs_x27_170_, v_i_164_, v_msg_168_);
v_i_164_ = v___x_172_;
v_bs_165_ = v___x_173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_175_, lean_object* v_i_176_, lean_object* v_bs_177_){
_start:
{
size_t v_sz_boxed_178_; size_t v_i_boxed_179_; lean_object* v_res_180_; 
v_sz_boxed_178_ = lean_unbox_usize(v_sz_175_);
lean_dec(v_sz_175_);
v_i_boxed_179_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_res_180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_boxed_178_, v_i_boxed_179_, v_bs_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_oldTraces_181_, lean_object* v_data_182_, lean_object* v_ref_183_, lean_object* v_msg_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_toCold_188_; lean_object* v_currRecDepth_189_; lean_object* v_ref_190_; uint16_t v_optionFlags_191_; uint8_t v_suppressElabErrors_192_; uint8_t v_isRecordingDeps_193_; lean_object* v_ref_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_traceState_197_; lean_object* v_traces_198_; lean_object* v___x_199_; size_t v_sz_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v_msg_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_243_; 
v_toCold_188_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_189_ = lean_ctor_get(v___y_185_, 1);
v_ref_190_ = lean_ctor_get(v___y_185_, 2);
v_optionFlags_191_ = lean_ctor_get_uint16(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_192_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 2);
v_isRecordingDeps_193_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 3);
v_ref_194_ = l_Lean_replaceRef(v_ref_183_, v_ref_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_toCold_188_);
v___x_195_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_195_, 0, v_toCold_188_);
lean_ctor_set(v___x_195_, 1, v_currRecDepth_189_);
lean_ctor_set(v___x_195_, 2, v_ref_194_);
lean_ctor_set_uint16(v___x_195_, sizeof(void*)*3, v_optionFlags_191_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 2, v_suppressElabErrors_192_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 3, v_isRecordingDeps_193_);
v___x_196_ = lean_st_ref_get(v___y_186_);
v_traceState_197_ = lean_ctor_get(v___x_196_, 4);
lean_inc_ref(v_traceState_197_);
lean_dec(v___x_196_);
v_traces_198_ = lean_ctor_get(v_traceState_197_, 0);
lean_inc_ref(v_traces_198_);
lean_dec_ref(v_traceState_197_);
v___x_199_ = l_Lean_PersistentArray_toArray___redArg(v_traces_198_);
lean_dec_ref(v_traces_198_);
v_sz_200_ = lean_array_size(v___x_199_);
v___x_201_ = ((size_t)0ULL);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_200_, v___x_201_, v___x_199_);
v_msg_203_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_203_, 0, v_data_182_);
lean_ctor_set(v_msg_203_, 1, v_msg_184_);
lean_ctor_set(v_msg_203_, 2, v___x_202_);
v___x_204_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_203_, v___x_195_, v___y_186_);
lean_dec_ref_known(v___x_195_, 3);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_243_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_243_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_243_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v_traceState_210_; lean_object* v_env_211_; lean_object* v_nextMacroScope_212_; lean_object* v_ngen_213_; lean_object* v_auxDeclNGen_214_; lean_object* v_cache_215_; lean_object* v_recordedDeps_216_; lean_object* v_messages_217_; lean_object* v_infoState_218_; lean_object* v_snapshotTasks_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_242_; 
v___x_209_ = lean_st_ref_take(v___y_186_);
v_traceState_210_ = lean_ctor_get(v___x_209_, 4);
v_env_211_ = lean_ctor_get(v___x_209_, 0);
v_nextMacroScope_212_ = lean_ctor_get(v___x_209_, 1);
v_ngen_213_ = lean_ctor_get(v___x_209_, 2);
v_auxDeclNGen_214_ = lean_ctor_get(v___x_209_, 3);
v_cache_215_ = lean_ctor_get(v___x_209_, 5);
v_recordedDeps_216_ = lean_ctor_get(v___x_209_, 6);
v_messages_217_ = lean_ctor_get(v___x_209_, 7);
v_infoState_218_ = lean_ctor_get(v___x_209_, 8);
v_snapshotTasks_219_ = lean_ctor_get(v___x_209_, 9);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_242_ == 0)
{
v___x_221_ = v___x_209_;
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snapshotTasks_219_);
lean_inc(v_infoState_218_);
lean_inc(v_messages_217_);
lean_inc(v_recordedDeps_216_);
lean_inc(v_cache_215_);
lean_inc(v_traceState_210_);
lean_inc(v_auxDeclNGen_214_);
lean_inc(v_ngen_213_);
lean_inc(v_nextMacroScope_212_);
lean_inc(v_env_211_);
lean_dec(v___x_209_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint64_t v_tid_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_240_; 
v_tid_223_ = lean_ctor_get_uint64(v_traceState_210_, sizeof(void*)*1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_traceState_210_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_traceState_210_, 0);
lean_dec(v_unused_241_);
v___x_225_ = v_traceState_210_;
v_isShared_226_ = v_isSharedCheck_240_;
goto v_resetjp_224_;
}
else
{
lean_dec(v_traceState_210_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_240_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_227_ = lean_box(0);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_ref_183_);
lean_ctor_set(v___x_228_, 1, v_a_205_);
v___x_229_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_181_, v___x_228_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_229_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_229_);
lean_ctor_set_uint64(v_reuseFailAlloc_239_, sizeof(void*)*1, v_tid_223_);
v___x_231_ = v_reuseFailAlloc_239_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 4, v___x_231_);
v___x_233_ = v___x_221_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_env_211_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_nextMacroScope_212_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_ngen_213_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_auxDeclNGen_214_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_cache_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_recordedDeps_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_messages_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v_infoState_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_snapshotTasks_219_);
v___x_233_ = v_reuseFailAlloc_238_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_186_, v___x_233_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_227_);
v___x_236_ = v___x_207_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_227_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_244_, lean_object* v_data_245_, lean_object* v_ref_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_244_, v_data_245_, v_ref_246_, v_msg_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v_x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v_x_252_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v_x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 1);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v_x_252_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v_x_252_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v_x_252_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 0);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_270_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_273_){
_start:
{
if (lean_obj_tag(v_e_273_) == 0)
{
uint8_t v___x_274_; 
v___x_274_ = 2;
return v___x_274_;
}
else
{
lean_object* v_a_275_; uint8_t v___x_276_; 
v_a_275_ = lean_ctor_get(v_e_273_, 0);
v___x_276_ = lean_unbox(v_a_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 1;
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_279_);
lean_dec_ref(v_e_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_282_; double v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_float_of_nat(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_287_; double v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1000u);
v___x_288_ = lean_float_of_nat(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_289_, uint8_t v_collapsed_290_, lean_object* v_tag_291_, lean_object* v_opts_292_, uint8_t v_clsEnabled_293_, lean_object* v_oldTraces_294_, lean_object* v_msg_295_, lean_object* v_resStartStop_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v_data_305_; lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___y_321_; lean_object* v_a_322_; uint8_t v___y_337_; double v___y_369_; 
v_fst_300_ = lean_ctor_get(v_resStartStop_296_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v_resStartStop_296_, 1);
lean_inc(v_snd_301_);
lean_dec_ref(v_resStartStop_296_);
v_fst_316_ = lean_ctor_get(v_snd_301_, 0);
lean_inc(v_fst_316_);
v_snd_317_ = lean_ctor_get(v_snd_301_, 1);
lean_inc(v_snd_317_);
lean_dec(v_snd_301_);
v___x_318_ = l_Lean_trace_profiler;
v___x_319_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_292_, v___x_318_);
if (v___x_319_ == 0)
{
v___y_337_ = v___x_319_;
goto v___jp_336_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = l_Lean_trace_profiler_useHeartbeats;
v___x_375_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_292_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; double v___x_378_; double v___x_379_; double v___x_380_; 
v___x_376_ = l_Lean_trace_profiler_threshold;
v___x_377_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_292_, v___x_376_);
v___x_378_ = lean_float_of_nat(v___x_377_);
v___x_379_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_380_ = lean_float_div(v___x_378_, v___x_379_);
v___y_369_ = v___x_380_;
goto v___jp_368_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; double v___x_383_; 
v___x_381_ = l_Lean_trace_profiler_threshold;
v___x_382_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_292_, v___x_381_);
v___x_383_ = lean_float_of_nat(v___x_382_);
v___y_369_ = v___x_383_;
goto v___jp_368_;
}
}
v___jp_302_:
{
lean_object* v___x_306_; 
lean_inc(v___y_304_);
v___x_306_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_294_, v_data_305_, v___y_304_, v___y_303_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_300_);
return v___x_307_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_fst_300_);
v_a_308_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
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
}
v___jp_320_:
{
uint8_t v_result_323_; lean_object* v___x_324_; lean_object* v___x_325_; double v___x_326_; lean_object* v_data_327_; 
v_result_323_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_300_);
v___x_324_ = lean_box(v_result_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
lean_inc_ref(v_tag_291_);
lean_inc_ref(v___x_325_);
lean_inc(v_cls_289_);
v_data_327_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_327_, 0, v_cls_289_);
lean_ctor_set(v_data_327_, 1, v___x_325_);
lean_ctor_set(v_data_327_, 2, v_tag_291_);
lean_ctor_set_float(v_data_327_, sizeof(void*)*3, v___x_326_);
lean_ctor_set_float(v_data_327_, sizeof(void*)*3 + 8, v___x_326_);
lean_ctor_set_uint8(v_data_327_, sizeof(void*)*3 + 16, v_collapsed_290_);
if (v___x_319_ == 0)
{
lean_dec_ref_known(v___x_325_, 1);
lean_dec(v_snd_317_);
lean_dec(v_fst_316_);
lean_dec_ref(v_tag_291_);
lean_dec(v_cls_289_);
v___y_303_ = v_a_322_;
v___y_304_ = v___y_321_;
v_data_305_ = v_data_327_;
goto v___jp_302_;
}
else
{
lean_object* v_data_328_; double v___x_329_; double v___x_330_; 
lean_dec_ref_known(v_data_327_, 3);
v_data_328_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_328_, 0, v_cls_289_);
lean_ctor_set(v_data_328_, 1, v___x_325_);
lean_ctor_set(v_data_328_, 2, v_tag_291_);
v___x_329_ = lean_unbox_float(v_fst_316_);
lean_dec(v_fst_316_);
lean_ctor_set_float(v_data_328_, sizeof(void*)*3, v___x_329_);
v___x_330_ = lean_unbox_float(v_snd_317_);
lean_dec(v_snd_317_);
lean_ctor_set_float(v_data_328_, sizeof(void*)*3 + 8, v___x_330_);
lean_ctor_set_uint8(v_data_328_, sizeof(void*)*3 + 16, v_collapsed_290_);
v___y_303_ = v_a_322_;
v___y_304_ = v___y_321_;
v_data_305_ = v_data_328_;
goto v___jp_302_;
}
}
v___jp_331_:
{
lean_object* v_ref_332_; lean_object* v___x_333_; 
v_ref_332_ = lean_ctor_get(v___y_297_, 2);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
lean_inc(v_fst_300_);
v___x_333_ = lean_apply_4(v_msg_295_, v_fst_300_, v___y_297_, v___y_298_, lean_box(0));
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___y_321_ = v_ref_332_;
v_a_322_ = v_a_334_;
goto v___jp_320_;
}
else
{
lean_object* v___x_335_; 
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
v___y_321_ = v_ref_332_;
v_a_322_ = v___x_335_;
goto v___jp_320_;
}
}
v___jp_336_:
{
if (v_clsEnabled_293_ == 0)
{
if (v___y_337_ == 0)
{
lean_object* v___x_338_; lean_object* v_traceState_339_; lean_object* v_env_340_; lean_object* v_nextMacroScope_341_; lean_object* v_ngen_342_; lean_object* v_auxDeclNGen_343_; lean_object* v_cache_344_; lean_object* v_recordedDeps_345_; lean_object* v_messages_346_; lean_object* v_infoState_347_; lean_object* v_snapshotTasks_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_snd_317_);
lean_dec(v_fst_316_);
lean_dec_ref(v_msg_295_);
lean_dec_ref(v_tag_291_);
lean_dec(v_cls_289_);
v___x_338_ = lean_st_ref_take(v___y_298_);
v_traceState_339_ = lean_ctor_get(v___x_338_, 4);
v_env_340_ = lean_ctor_get(v___x_338_, 0);
v_nextMacroScope_341_ = lean_ctor_get(v___x_338_, 1);
v_ngen_342_ = lean_ctor_get(v___x_338_, 2);
v_auxDeclNGen_343_ = lean_ctor_get(v___x_338_, 3);
v_cache_344_ = lean_ctor_get(v___x_338_, 5);
v_recordedDeps_345_ = lean_ctor_get(v___x_338_, 6);
v_messages_346_ = lean_ctor_get(v___x_338_, 7);
v_infoState_347_ = lean_ctor_get(v___x_338_, 8);
v_snapshotTasks_348_ = lean_ctor_get(v___x_338_, 9);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_367_ == 0)
{
v___x_350_ = v___x_338_;
v_isShared_351_ = v_isSharedCheck_367_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snapshotTasks_348_);
lean_inc(v_infoState_347_);
lean_inc(v_messages_346_);
lean_inc(v_recordedDeps_345_);
lean_inc(v_cache_344_);
lean_inc(v_traceState_339_);
lean_inc(v_auxDeclNGen_343_);
lean_inc(v_ngen_342_);
lean_inc(v_nextMacroScope_341_);
lean_inc(v_env_340_);
lean_dec(v___x_338_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_367_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint64_t v_tid_352_; lean_object* v_traces_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_366_; 
v_tid_352_ = lean_ctor_get_uint64(v_traceState_339_, sizeof(void*)*1);
v_traces_353_ = lean_ctor_get(v_traceState_339_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_traceState_339_);
if (v_isSharedCheck_366_ == 0)
{
v___x_355_ = v_traceState_339_;
v_isShared_356_ = v_isSharedCheck_366_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_traces_353_);
lean_dec(v_traceState_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_366_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_294_, v_traces_353_);
lean_dec_ref(v_traces_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_357_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_357_);
lean_ctor_set_uint64(v_reuseFailAlloc_365_, sizeof(void*)*1, v_tid_352_);
v___x_359_ = v_reuseFailAlloc_365_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 4, v___x_359_);
v___x_361_ = v___x_350_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_env_340_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_341_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_ngen_342_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_343_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v_cache_344_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_recordedDeps_345_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_messages_346_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_infoState_347_);
lean_ctor_set(v_reuseFailAlloc_364_, 9, v_snapshotTasks_348_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_st_ref_put(v___y_298_, v___x_361_);
v___x_363_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_300_);
return v___x_363_;
}
}
}
}
}
else
{
goto v___jp_331_;
}
}
else
{
goto v___jp_331_;
}
}
v___jp_368_:
{
double v___x_370_; double v___x_371_; double v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_unbox_float(v_snd_317_);
v___x_371_ = lean_unbox_float(v_fst_316_);
v___x_372_ = lean_float_sub(v___x_370_, v___x_371_);
v___x_373_ = lean_float_decLt(v___y_369_, v___x_372_);
v___y_337_ = v___x_373_;
goto v___jp_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_384_, lean_object* v_collapsed_385_, lean_object* v_tag_386_, lean_object* v_opts_387_, lean_object* v_clsEnabled_388_, lean_object* v_oldTraces_389_, lean_object* v_msg_390_, lean_object* v_resStartStop_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_collapsed_boxed_395_; uint8_t v_clsEnabled_boxed_396_; lean_object* v_res_397_; 
v_collapsed_boxed_395_ = lean_unbox(v_collapsed_385_);
v_clsEnabled_boxed_396_ = lean_unbox(v_clsEnabled_388_);
v_res_397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_384_, v_collapsed_boxed_395_, v_tag_386_, v_opts_387_, v_clsEnabled_boxed_396_, v_oldTraces_389_, v_msg_390_, v_resStartStop_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v_opts_387_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_398_, lean_object* v_as_399_, size_t v_i_400_, size_t v_stop_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = lean_usize_dec_eq(v_i_400_, v_stop_401_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; lean_object* v___x_5263__overap_407_; lean_object* v___x_408_; 
v___x_406_ = 1;
v___x_5263__overap_407_ = lean_array_uget_borrowed(v_as_399_, v_i_400_);
lean_inc(v___x_5263__overap_407_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v_name_398_);
v___x_408_ = lean_apply_4(v___x_5263__overap_407_, v_name_398_, v___y_402_, v___y_403_, lean_box(0));
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; 
v___x_413_ = lean_unbox(v_a_409_);
lean_dec(v_a_409_);
if (v___x_413_ == 0)
{
size_t v___x_414_; size_t v___x_415_; 
lean_del_object(v___x_411_);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_400_, v___x_414_);
v_i_400_ = v___x_415_;
goto _start;
}
else
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_name_398_);
v___x_417_ = lean_box(v___x_406_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_417_);
v___x_419_ = v___x_411_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec(v_name_398_);
return v___x_408_;
}
}
else
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_name_398_);
v___x_422_ = 0;
v___x_423_ = lean_box(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_425_, lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
size_t v_i_boxed_432_; size_t v_stop_boxed_433_; lean_object* v_res_434_; 
v_i_boxed_432_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_433_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_425_, v_as_426_, v_i_boxed_432_, v_stop_boxed_433_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_as_426_);
return v_res_434_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_443_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_444_ = l_Lean_Name_append(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_445_; double v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1000000000u);
v___x_446_ = lean_float_of_nat(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_toCold_451_; lean_object* v_options_452_; lean_object* v_inheritedTraceOptions_453_; uint8_t v_hasTrace_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___y_458_; 
v_toCold_451_ = lean_ctor_get(v_a_448_, 0);
v_options_452_ = lean_ctor_get(v_toCold_451_, 2);
v_inheritedTraceOptions_453_ = lean_ctor_get(v_toCold_451_, 11);
v_hasTrace_454_ = lean_ctor_get_uint8(v_options_452_, sizeof(void*)*1);
v___x_455_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_456_ = lean_box(0);
if (v_hasTrace_454_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_st_ref_get(v___x_455_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v___x_475_);
v___x_478_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v___x_475_);
lean_dec(v_name_447_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_456_);
return v___x_479_;
}
else
{
if (v___x_478_ == 0)
{
lean_object* v___x_480_; 
lean_dec(v___x_475_);
lean_dec(v_name_447_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_456_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_477_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_447_, v___x_475_, v___x_481_, v___x_482_, v_a_448_, v_a_449_);
lean_dec(v___x_475_);
v___y_458_ = v___x_483_;
goto v___jp_457_;
}
}
}
else
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v_a_492_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v_a_507_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v_a_513_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v_a_525_; 
lean_inc(v_name_447_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_484_, 0, v_name_447_);
v___x_485_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_486_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_487_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_453_, v_options_452_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = l_Lean_trace_profiler;
v___x_570_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_452_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
lean_dec_ref(v___f_484_);
v___x_571_ = lean_st_ref_get(v___x_455_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_array_get_size(v___x_571_);
v___x_574_ = lean_nat_dec_lt(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_571_);
lean_dec(v_name_447_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_456_);
return v___x_575_;
}
else
{
if (v___x_574_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_571_);
lean_dec(v_name_447_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_456_);
return v___x_576_;
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_573_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_447_, v___x_571_, v___x_577_, v___x_578_, v_a_448_, v_a_449_);
lean_dec(v___x_571_);
v___y_458_ = v___x_579_;
goto v___jp_457_;
}
}
}
else
{
goto v___jp_528_;
}
}
else
{
goto v___jp_528_;
}
v___jp_489_:
{
lean_object* v___x_493_; double v___x_494_; double v___x_495_; double v___x_496_; double v___x_497_; double v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_493_ = lean_io_mono_nanos_now();
v___x_494_ = lean_float_of_nat(v___y_491_);
v___x_495_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_496_ = lean_float_div(v___x_494_, v___x_495_);
v___x_497_ = lean_float_of_nat(v___x_493_);
v___x_498_ = lean_float_div(v___x_497_, v___x_495_);
v___x_499_ = lean_box_float(v___x_496_);
v___x_500_ = lean_box_float(v___x_498_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_492_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_485_, v_hasTrace_454_, v___x_486_, v_options_452_, v___x_488_, v___y_490_, v___f_484_, v___x_502_, v_a_448_, v_a_449_);
v___y_458_ = v___x_503_;
goto v___jp_457_;
}
v___jp_504_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_box(v_a_507_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
v___y_490_ = v___y_505_;
v___y_491_ = v___y_506_;
v_a_492_ = v___x_509_;
goto v___jp_489_;
}
v___jp_510_:
{
lean_object* v___x_514_; double v___x_515_; double v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_514_ = lean_io_get_num_heartbeats();
v___x_515_ = lean_float_of_nat(v___y_512_);
v___x_516_ = lean_float_of_nat(v___x_514_);
v___x_517_ = lean_box_float(v___x_515_);
v___x_518_ = lean_box_float(v___x_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_513_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_485_, v_hasTrace_454_, v___x_486_, v_options_452_, v___x_488_, v___y_511_, v___f_484_, v___x_520_, v_a_448_, v_a_449_);
v___y_458_ = v___x_521_;
goto v___jp_457_;
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(v_a_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___y_511_ = v___y_523_;
v___y_512_ = v___y_524_;
v_a_513_ = v___x_527_;
goto v___jp_510_;
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v_a_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_449_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_trace_profiler_useHeartbeats;
v___x_532_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_452_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_533_ = lean_io_mono_nanos_now();
v___x_534_ = lean_st_ref_get(v___x_455_);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_array_get_size(v___x_534_);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec(v___x_534_);
lean_dec(v_name_447_);
v___y_505_ = v_a_530_;
v___y_506_ = v___x_533_;
v_a_507_ = v___x_537_;
goto v___jp_504_;
}
else
{
if (v___x_537_ == 0)
{
lean_dec(v___x_534_);
lean_dec(v_name_447_);
v___y_505_ = v_a_530_;
v___y_506_ = v___x_533_;
v_a_507_ = v___x_537_;
goto v___jp_504_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_447_, v___x_534_, v___x_538_, v___x_539_, v_a_448_, v_a_449_);
lean_dec(v___x_534_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint8_t v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = lean_unbox(v_a_541_);
lean_dec(v_a_541_);
v___y_505_ = v_a_530_;
v___y_506_ = v___x_533_;
v_a_507_ = v___x_542_;
goto v___jp_504_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_540_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_490_ = v_a_530_;
v___y_491_ = v___x_533_;
v_a_492_ = v___x_548_;
goto v___jp_489_;
}
}
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_551_ = lean_io_get_num_heartbeats();
v___x_552_ = lean_st_ref_get(v___x_455_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_array_get_size(v___x_552_);
v___x_555_ = lean_nat_dec_lt(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_name_447_);
v___y_523_ = v_a_530_;
v___y_524_ = v___x_551_;
v_a_525_ = v___x_555_;
goto v___jp_522_;
}
else
{
if (v___x_555_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_name_447_);
v___y_523_ = v_a_530_;
v___y_524_ = v___x_551_;
v_a_525_ = v___x_555_;
goto v___jp_522_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_447_, v___x_552_, v___x_556_, v___x_557_, v_a_448_, v_a_449_);
lean_dec(v___x_552_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_unbox(v_a_559_);
lean_dec(v_a_559_);
v___y_523_ = v_a_530_;
v___y_524_ = v___x_551_;
v_a_525_ = v___x_560_;
goto v___jp_522_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_558_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v___y_511_ = v_a_530_;
v___y_512_ = v___x_551_;
v_a_513_ = v___x_566_;
goto v___jp_510_;
}
}
}
}
}
}
}
}
v___jp_457_:
{
if (lean_obj_tag(v___y_458_) == 0)
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_isSharedCheck_465_ = !lean_is_exclusive(v___y_458_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___y_458_, 0);
lean_dec(v_unused_466_);
v___x_460_ = v___y_458_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_dec(v___y_458_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_456_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_456_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_a_467_ = lean_ctor_get(v___y_458_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___y_458_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___y_458_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___y_458_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_executeReservedNameAction(v_name_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_585_, lean_object* v_x_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_586_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_591_, lean_object* v_x_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_591_, v_x_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_604_, uint8_t v___y_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 1)
{
lean_object* v_pre_607_; 
v_pre_607_ = lean_ctor_get(v_x_606_, 0);
switch(lean_obj_tag(v_pre_607_))
{
case 1:
{
lean_object* v_pre_608_; 
v_pre_608_ = lean_ctor_get(v_pre_607_, 0);
switch(lean_obj_tag(v_pre_608_))
{
case 0:
{
lean_object* v_str_609_; lean_object* v_str_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_str_609_ = lean_ctor_get(v_x_606_, 1);
v_str_610_ = lean_ctor_get(v_pre_607_, 1);
v___x_611_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_612_ = lean_string_dec_eq(v_str_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_614_ = lean_string_dec_eq(v_str_610_, v___x_613_);
if (v___x_614_ == 0)
{
return v___x_614_;
}
else
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_616_ = lean_string_dec_eq(v_str_609_, v___x_615_);
if (v___x_616_ == 0)
{
return v___x_616_;
}
else
{
return v_suppressElabErrors_604_;
}
}
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_618_ = lean_string_dec_eq(v_str_609_, v___x_617_);
if (v___x_618_ == 0)
{
return v___x_618_;
}
else
{
return v_suppressElabErrors_604_;
}
}
}
case 1:
{
lean_object* v_pre_619_; 
v_pre_619_ = lean_ctor_get(v_pre_608_, 0);
if (lean_obj_tag(v_pre_619_) == 0)
{
lean_object* v_str_620_; lean_object* v_str_621_; lean_object* v_str_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_str_620_ = lean_ctor_get(v_x_606_, 1);
v_str_621_ = lean_ctor_get(v_pre_607_, 1);
v_str_622_ = lean_ctor_get(v_pre_608_, 1);
v___x_623_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_624_ = lean_string_dec_eq(v_str_622_, v___x_623_);
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_626_ = lean_string_dec_eq(v_str_621_, v___x_625_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_628_ = lean_string_dec_eq(v_str_620_, v___x_627_);
if (v___x_628_ == 0)
{
return v___x_628_;
}
else
{
return v_suppressElabErrors_604_;
}
}
}
}
else
{
return v___y_605_;
}
}
default: 
{
return v___y_605_;
}
}
}
case 0:
{
lean_object* v_str_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_str_629_ = lean_ctor_get(v_x_606_, 1);
v___x_630_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_631_ = lean_string_dec_eq(v_str_629_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
return v_suppressElabErrors_604_;
}
}
default: 
{
return v___y_605_;
}
}
}
else
{
return v___y_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_632_, lean_object* v___y_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_suppressElabErrors_boxed_635_; uint8_t v___y_5030__boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_suppressElabErrors_boxed_635_ = lean_unbox(v_suppressElabErrors_632_);
v___y_5030__boxed_636_ = lean_unbox(v___y_633_);
v_res_637_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_635_, v___y_5030__boxed_636_, v_x_634_);
lean_dec(v_x_634_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_639_, lean_object* v_msgData_640_, uint8_t v_severity_641_, uint8_t v_isSilent_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; uint8_t v___y_652_; lean_object* v___y_653_; lean_object* v_toCold_654_; lean_object* v___y_655_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; uint8_t v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; uint8_t v___x_734_; uint8_t v___y_736_; uint8_t v___y_737_; uint8_t v___y_738_; uint8_t v___y_740_; uint8_t v___x_748_; 
v___x_734_ = 2;
v___x_748_ = l_Lean_instBEqMessageSeverity_beq(v_severity_641_, v___x_734_);
if (v___x_748_ == 0)
{
v___y_740_ = v___x_748_;
goto v___jp_739_;
}
else
{
uint8_t v___x_749_; 
lean_inc_ref(v_msgData_640_);
v___x_749_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_640_);
v___y_740_ = v___x_749_;
goto v___jp_739_;
}
v___jp_646_:
{
lean_object* v_currNamespace_656_; lean_object* v_openDecls_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v_nextMacroScope_663_; lean_object* v_ngen_664_; lean_object* v_auxDeclNGen_665_; lean_object* v_traceState_666_; lean_object* v_cache_667_; lean_object* v_recordedDeps_668_; lean_object* v_messages_669_; lean_object* v_infoState_670_; lean_object* v_snapshotTasks_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_682_; 
v_currNamespace_656_ = lean_ctor_get(v_toCold_654_, 4);
v_openDecls_657_ = lean_ctor_get(v_toCold_654_, 5);
lean_inc(v_openDecls_657_);
lean_inc(v_currNamespace_656_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_currNamespace_656_);
lean_ctor_set(v___x_658_, 1, v_openDecls_657_);
v___x_659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___y_648_);
lean_inc_ref(v___y_653_);
lean_inc_ref(v___y_647_);
v___x_660_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_660_, 0, v___y_647_);
lean_ctor_set(v___x_660_, 1, v___y_651_);
lean_ctor_set(v___x_660_, 2, v___y_649_);
lean_ctor_set(v___x_660_, 3, v___y_653_);
lean_ctor_set(v___x_660_, 4, v___x_659_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5, v___y_652_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5 + 1, v___y_650_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5 + 2, v_isSilent_642_);
v___x_661_ = lean_st_ref_take(v___y_655_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
v_nextMacroScope_663_ = lean_ctor_get(v___x_661_, 1);
v_ngen_664_ = lean_ctor_get(v___x_661_, 2);
v_auxDeclNGen_665_ = lean_ctor_get(v___x_661_, 3);
v_traceState_666_ = lean_ctor_get(v___x_661_, 4);
v_cache_667_ = lean_ctor_get(v___x_661_, 5);
v_recordedDeps_668_ = lean_ctor_get(v___x_661_, 6);
v_messages_669_ = lean_ctor_get(v___x_661_, 7);
v_infoState_670_ = lean_ctor_get(v___x_661_, 8);
v_snapshotTasks_671_ = lean_ctor_get(v___x_661_, 9);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_682_ == 0)
{
v___x_673_ = v___x_661_;
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snapshotTasks_671_);
lean_inc(v_infoState_670_);
lean_inc(v_messages_669_);
lean_inc(v_recordedDeps_668_);
lean_inc(v_cache_667_);
lean_inc(v_traceState_666_);
lean_inc(v_auxDeclNGen_665_);
lean_inc(v_ngen_664_);
lean_inc(v_nextMacroScope_663_);
lean_inc(v_env_662_);
lean_dec(v___x_661_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_MessageLog_add(v___x_660_, v_messages_669_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 7, v___x_676_);
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_env_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_nextMacroScope_663_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_ngen_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_auxDeclNGen_665_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_traceState_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_cache_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_recordedDeps_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_infoState_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_snapshotTasks_671_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_st_ref_put(v___y_655_, v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_675_);
return v___x_680_;
}
}
}
v___jp_683_:
{
lean_object* v_fileName_692_; lean_object* v_fileMap_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_709_; 
v_fileName_692_ = lean_ctor_get(v___y_688_, 0);
v_fileMap_693_ = lean_ctor_get(v___y_688_, 1);
v___x_694_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_640_);
v___x_695_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_694_, v___y_643_, v___y_644_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_709_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_709_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc_ref_n(v_fileMap_693_, 2);
v___x_700_ = l_Lean_FileMap_toPosition(v_fileMap_693_, v___y_690_);
lean_dec(v___y_690_);
v___x_701_ = l_Lean_FileMap_toPosition(v_fileMap_693_, v___y_691_);
lean_dec(v___y_691_);
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_689_ == 0)
{
lean_del_object(v___x_698_);
lean_dec_ref(v___y_684_);
v___y_647_ = v_fileName_692_;
v___y_648_ = v_a_696_;
v___y_649_ = v___x_702_;
v___y_650_ = v___y_686_;
v___y_651_ = v___x_700_;
v___y_652_ = v___y_687_;
v___y_653_ = v___x_703_;
v_toCold_654_ = v___y_685_;
v___y_655_ = v___y_644_;
goto v___jp_646_;
}
else
{
uint8_t v___x_704_; 
lean_inc(v_a_696_);
v___x_704_ = l_Lean_MessageData_hasTag(v___y_684_, v_a_696_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec_ref_known(v___x_702_, 1);
lean_dec_ref(v___x_700_);
lean_dec(v_a_696_);
v___x_705_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_705_);
v___x_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_del_object(v___x_698_);
v___y_647_ = v_fileName_692_;
v___y_648_ = v_a_696_;
v___y_649_ = v___x_702_;
v___y_650_ = v___y_686_;
v___y_651_ = v___x_700_;
v___y_652_ = v___y_687_;
v___y_653_ = v___x_703_;
v_toCold_654_ = v___y_685_;
v___y_655_ = v___y_644_;
goto v___jp_646_;
}
}
}
}
v___jp_710_:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Syntax_getTailPos_x3f(v___y_714_, v___y_716_);
lean_dec(v___y_714_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_inc(v___y_717_);
v___y_684_ = v___y_711_;
v___y_685_ = v___y_712_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_712_;
v___y_689_ = v___y_713_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_717_;
goto v___jp_683_;
}
else
{
lean_object* v_val_719_; 
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_718_, 1);
v___y_684_ = v___y_711_;
v___y_685_ = v___y_712_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_712_;
v___y_689_ = v___y_713_;
v___y_690_ = v___y_717_;
v___y_691_ = v_val_719_;
goto v___jp_683_;
}
}
v___jp_720_:
{
lean_object* v_toCold_724_; lean_object* v_ref_725_; uint8_t v_suppressElabErrors_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___f_729_; lean_object* v_ref_730_; lean_object* v___x_731_; 
v_toCold_724_ = lean_ctor_get(v___y_643_, 0);
v_ref_725_ = lean_ctor_get(v___y_643_, 2);
v_suppressElabErrors_726_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*3 + 2);
v___x_727_ = lean_box(v_suppressElabErrors_726_);
v___x_728_ = lean_box(v___y_721_);
v___f_729_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_729_, 0, v___x_727_);
lean_closure_set(v___f_729_, 1, v___x_728_);
v_ref_730_ = l_Lean_replaceRef(v_ref_639_, v_ref_725_);
v___x_731_ = l_Lean_Syntax_getPos_x3f(v_ref_730_, v___y_722_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_711_ = v___f_729_;
v___y_712_ = v_toCold_724_;
v___y_713_ = v_suppressElabErrors_726_;
v___y_714_ = v_ref_730_;
v___y_715_ = v___y_723_;
v___y_716_ = v___y_722_;
v___y_717_ = v___x_732_;
goto v___jp_710_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v___x_731_, 1);
v___y_711_ = v___f_729_;
v___y_712_ = v_toCold_724_;
v___y_713_ = v_suppressElabErrors_726_;
v___y_714_ = v_ref_730_;
v___y_715_ = v___y_723_;
v___y_716_ = v___y_722_;
v___y_717_ = v_val_733_;
goto v___jp_710_;
}
}
v___jp_735_:
{
if (v___y_738_ == 0)
{
v___y_721_ = v___y_736_;
v___y_722_ = v___y_737_;
v___y_723_ = v_severity_641_;
goto v___jp_720_;
}
else
{
v___y_721_ = v___y_736_;
v___y_722_ = v___y_737_;
v___y_723_ = v___x_734_;
goto v___jp_720_;
}
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = 1;
v___x_742_ = l_Lean_instBEqMessageSeverity_beq(v_severity_641_, v___x_741_);
if (v___x_742_ == 0)
{
v___y_736_ = v___y_740_;
v___y_737_ = v___y_740_;
v___y_738_ = v___x_742_;
goto v___jp_735_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_643_);
v___x_744_ = l_Lean_warningAsError;
v___x_745_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_743_, v___x_744_);
lean_dec_ref(v___x_743_);
v___y_736_ = v___y_740_;
v___y_737_ = v___y_740_;
v___y_738_ = v___x_745_;
goto v___jp_735_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_msgData_640_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_750_, lean_object* v_msgData_751_, lean_object* v_severity_752_, lean_object* v_isSilent_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
uint8_t v_severity_boxed_757_; uint8_t v_isSilent_boxed_758_; lean_object* v_res_759_; 
v_severity_boxed_757_ = lean_unbox(v_severity_752_);
v_isSilent_boxed_758_ = lean_unbox(v_isSilent_753_);
v_res_759_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_750_, v_msgData_751_, v_severity_boxed_757_, v_isSilent_boxed_758_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v_ref_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_760_, uint8_t v_severity_761_, uint8_t v_isSilent_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_ref_766_; lean_object* v___x_767_; 
v_ref_766_ = lean_ctor_get(v___y_763_, 2);
v___x_767_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_766_, v_msgData_760_, v_severity_761_, v_isSilent_762_, v___y_763_, v___y_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_768_, lean_object* v_severity_769_, lean_object* v_isSilent_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_severity_boxed_774_; uint8_t v_isSilent_boxed_775_; lean_object* v_res_776_; 
v_severity_boxed_774_ = lean_unbox(v_severity_769_);
v_isSilent_boxed_775_ = lean_unbox(v_isSilent_770_);
v_res_776_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_768_, v_severity_boxed_774_, v_isSilent_boxed_775_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = 2;
v___x_782_ = 0;
v___x_783_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_777_, v___x_781_, v___x_782_, v___y_778_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v___x_801_; 
lean_dec(v_id_795_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_x_797_);
return v___x_801_;
}
else
{
lean_object* v_head_802_; lean_object* v_tail_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_854_; 
v_head_802_ = lean_ctor_get(v_x_796_, 0);
v_tail_803_ = lean_ctor_get(v_x_796_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_854_ == 0)
{
v___x_805_ = v_x_796_;
v_isShared_806_ = v_isSharedCheck_854_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_tail_803_);
lean_inc(v_head_802_);
lean_dec(v_x_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_854_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___y_808_; uint8_t v___y_809_; uint8_t v_a_835_; lean_object* v_fst_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v_env_840_; uint8_t v___x_841_; uint8_t v___y_843_; 
v_fst_837_ = lean_ctor_get(v_head_802_, 0);
v___x_838_ = 1;
v___x_839_ = lean_st_ref_get(v___y_799_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref_n(v_env_840_, 2);
lean_dec(v___x_839_);
lean_inc(v_fst_837_);
v___x_841_ = l_Lean_Environment_contains(v_env_840_, v_fst_837_, v___x_838_);
if (v___x_841_ == 0)
{
uint8_t v_isExporting_851_; 
v_isExporting_851_ = lean_ctor_get_uint8(v_env_840_, sizeof(void*)*13);
if (v_isExporting_851_ == 0)
{
lean_dec_ref(v_env_840_);
v___y_843_ = v___x_841_;
goto v___jp_842_;
}
else
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = l_Lean_Environment_setExporting(v_env_840_, v___x_841_);
v___x_853_ = l_Lean_Environment_isImportedConst(v___x_852_, v_fst_837_);
lean_dec_ref(v___x_852_);
v___y_843_ = v___x_853_;
goto v___jp_842_;
}
}
else
{
lean_dec_ref(v_env_840_);
goto v___jp_829_;
}
v___jp_807_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_810_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_795_);
v___x_811_ = l_Lean_MessageData_ofName(v_id_795_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_Exception_toMessageData(v___y_808_);
v___x_816_ = l_Lean_indentD(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_817_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref_known(v___x_818_, 1);
v_x_796_ = v_tail_803_;
goto _start;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_tail_803_);
lean_dec(v_x_797_);
lean_dec(v_id_795_);
v_a_820_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_818_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v___x_828_; 
lean_dec(v_tail_803_);
lean_dec(v_x_797_);
lean_dec(v_id_795_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___y_808_);
return v___x_828_;
}
}
v___jp_829_:
{
lean_object* v___x_831_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_x_797_);
v___x_831_ = v___x_805_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_head_802_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_x_797_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v_x_796_ = v_tail_803_;
v_x_797_ = v___x_831_;
goto _start;
}
}
v___jp_834_:
{
if (v_a_835_ == 0)
{
lean_del_object(v___x_805_);
lean_dec(v_head_802_);
v_x_796_ = v_tail_803_;
goto _start;
}
else
{
goto v___jp_829_;
}
}
v___jp_842_:
{
if (v___y_843_ == 0)
{
lean_object* v___x_844_; 
lean_inc(v_fst_837_);
v___x_844_ = l_Lean_executeReservedNameAction(v_fst_837_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; lean_object* v_env_846_; uint8_t v___x_847_; 
lean_dec_ref_known(v___x_844_, 1);
v___x_845_ = lean_st_ref_get(v___y_799_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v___x_847_ = l_Lean_Environment_containsOnBranch(v_env_846_, v_fst_837_);
lean_dec_ref(v_env_846_);
v_a_835_ = v___x_847_;
goto v___jp_834_;
}
else
{
lean_object* v_a_848_; uint8_t v___x_849_; 
lean_del_object(v___x_805_);
lean_dec(v_head_802_);
v_a_848_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_844_, 1);
v___x_849_ = l_Lean_Exception_isInterrupt(v_a_848_);
if (v___x_849_ == 0)
{
uint8_t v___x_850_; 
lean_inc(v_a_848_);
v___x_850_ = l_Lean_Exception_isRuntime(v_a_848_);
v___y_808_ = v_a_848_;
v___y_809_ = v___x_850_;
goto v___jp_807_;
}
else
{
v___y_808_ = v_a_848_;
v___y_809_ = v___x_849_;
goto v___jp_807_;
}
}
}
else
{
v_a_835_ = v___x_841_;
goto v___jp_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_855_, v_x_856_, v_x_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_head_864_; lean_object* v_tail_865_; lean_object* v_fst_866_; uint8_t v___x_867_; 
v_head_864_ = lean_ctor_get(v_x_862_, 0);
v_tail_865_ = lean_ctor_get(v_x_862_, 1);
v_fst_866_ = lean_ctor_get(v_head_864_, 0);
v___x_867_ = l_Lean_isPrivateName(v_fst_866_);
if (v___x_867_ == 0)
{
v_x_862_ = v_tail_865_;
goto _start;
}
else
{
lean_object* v___x_869_; 
lean_inc(v_head_864_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v_head_864_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_870_);
lean_dec(v_x_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; 
v___x_876_ = 1;
v___x_877_ = 0;
v___x_878_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_872_, v___x_876_, v___x_877_, v___y_873_, v___y_874_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_885_);
v___x_888_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_887_, v_opt_884_);
lean_dec_ref(v___x_887_);
v___x_889_ = lean_box(v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_891_, v___y_892_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_opt_891_);
return v_res_894_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_env_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_928_; 
v___x_905_ = lean_st_ref_get(v___y_903_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_906_);
lean_dec(v___x_905_);
v___x_907_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_908_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_907_, v___y_902_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_928_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_928_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_928_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v_isExporting_918_; 
v_isExporting_918_ = lean_ctor_get_uint8(v_env_906_, sizeof(void*)*13);
lean_dec_ref(v_env_906_);
if (v_isExporting_918_ == 0)
{
lean_dec(v_a_909_);
lean_dec(v_id_901_);
goto v___jp_913_;
}
else
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_isPrivateName(v_id_901_);
if (v___x_919_ == 0)
{
lean_dec(v_a_909_);
lean_dec(v_id_901_);
goto v___jp_913_;
}
else
{
uint8_t v___x_920_; 
v___x_920_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
if (v___x_920_ == 0)
{
lean_dec(v_id_901_);
goto v___jp_913_;
}
else
{
lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_911_);
v___x_921_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_922_ = 0;
v___x_923_ = l_Lean_MessageData_ofConstName(v_id_901_, v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_926_, v___y_902_, v___y_903_);
return v___x_927_;
}
}
}
v___jp_913_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_box(0);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_914_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_934_, uint8_t v_enableLog_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_toCold_940_; lean_object* v_env_941_; lean_object* v_currNamespace_942_; lean_object* v_openDecls_943_; lean_object* v___x_944_; lean_object* v_res_945_; lean_object* v___x_946_; 
v___x_939_ = lean_st_ref_get(v___y_937_);
v_toCold_940_ = lean_ctor_get(v___y_936_, 0);
v_env_941_ = lean_ctor_get(v___x_939_, 0);
lean_inc_ref(v_env_941_);
lean_dec(v___x_939_);
v_currNamespace_942_ = lean_ctor_get(v_toCold_940_, 4);
v_openDecls_943_ = lean_ctor_get(v_toCold_940_, 5);
v___x_944_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_936_);
lean_inc(v_openDecls_943_);
lean_inc(v_currNamespace_942_);
v_res_945_ = l_Lean_ResolveName_resolveGlobalName(v_env_941_, v___x_944_, v_currNamespace_942_, v_openDecls_943_, v_id_934_);
lean_dec_ref(v___x_944_);
v___x_946_ = lean_st_ref_get(v___y_937_);
if (v_enableLog_935_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v___x_946_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_res_945_);
return v___x_947_;
}
else
{
lean_object* v_env_948_; uint8_t v_isExporting_949_; 
v_env_948_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_946_);
v_isExporting_949_ = lean_ctor_get_uint8(v_env_948_, sizeof(void*)*13);
lean_dec_ref(v_env_948_);
if (v_isExporting_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_res_945_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_945_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; lean_object* v_fst_953_; lean_object* v___x_954_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
v_fst_953_ = lean_ctor_get(v_val_952_, 0);
lean_inc(v_fst_953_);
lean_dec(v_val_952_);
v___x_954_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_953_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_962_);
v___x_956_ = v___x_954_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_dec(v___x_954_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_res_945_);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_res_945_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_res_945_);
v_a_963_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_954_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_954_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v___x_951_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_res_945_);
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_972_, lean_object* v_enableLog_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v_enableLog_boxed_977_; lean_object* v_res_978_; 
v_enableLog_boxed_977_ = lean_unbox(v_enableLog_973_);
v_res_978_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_972_, v_enableLog_boxed_977_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
uint8_t v___x_983_; lean_object* v___x_984_; 
v___x_983_ = 1;
lean_inc(v_id_979_);
v___x_984_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_979_, v___x_983_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = lean_box(0);
v___x_987_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_979_, v_a_985_, v___x_986_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = l_List_reverse___redArg(v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
return v___x_987_;
}
}
else
{
lean_dec(v_id_979_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_realizeGlobalName(v_id_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1002_, v___y_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v_opt_1007_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
if (lean_obj_tag(v_a_1012_) == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_reverse___redArg(v_a_1013_);
return v___x_1014_;
}
else
{
lean_object* v_head_1015_; lean_object* v_tail_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1025_; 
v_head_1015_ = lean_ctor_get(v_a_1012_, 0);
v_tail_1016_ = lean_ctor_get(v_a_1012_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1018_ = v_a_1012_;
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_tail_1016_);
lean_inc(v_head_1015_);
lean_dec(v_a_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_fst_1020_; lean_object* v___x_1022_; 
v_fst_1020_ = lean_ctor_get(v_head_1015_, 0);
lean_inc(v_fst_1020_);
lean_dec(v_head_1015_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_a_1013_);
lean_ctor_set(v___x_1018_, 0, v_fst_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_fst_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1013_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v_a_1012_ = v_tail_1016_;
v_a_1013_ = v___x_1022_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_ref_1030_; lean_object* v___x_1031_; lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_ref_1030_ = lean_ctor_get(v___y_1027_, 2);
v___x_1031_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1026_, v___y_1027_, v___y_1028_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_inc(v_ref_1030_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_ref_1030_);
lean_ctor_set(v___x_1036_, 1, v_a_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_toCold_1051_; lean_object* v_currRecDepth_1052_; lean_object* v_ref_1053_; uint16_t v_optionFlags_1054_; uint8_t v_suppressElabErrors_1055_; uint8_t v_isRecordingDeps_1056_; lean_object* v_ref_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_toCold_1051_ = lean_ctor_get(v___y_1048_, 0);
v_currRecDepth_1052_ = lean_ctor_get(v___y_1048_, 1);
v_ref_1053_ = lean_ctor_get(v___y_1048_, 2);
v_optionFlags_1054_ = lean_ctor_get_uint16(v___y_1048_, sizeof(void*)*3);
v_suppressElabErrors_1055_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1056_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 3);
v_ref_1057_ = l_Lean_replaceRef(v_ref_1046_, v_ref_1053_);
lean_inc(v_currRecDepth_1052_);
lean_inc_ref(v_toCold_1051_);
v___x_1058_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1058_, 0, v_toCold_1051_);
lean_ctor_set(v___x_1058_, 1, v_currRecDepth_1052_);
lean_ctor_set(v___x_1058_, 2, v_ref_1057_);
lean_ctor_set_uint16(v___x_1058_, sizeof(void*)*3, v_optionFlags_1054_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*3 + 2, v_suppressElabErrors_1055_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*3 + 3, v_isRecordingDeps_1056_);
v___x_1059_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1047_, v___x_1058_, v___y_1049_);
lean_dec_ref_known(v___x_1058_, 3);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1060_, v_msg_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v_ref_1060_);
return v_res_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1099_, lean_object* v_declHint_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_env_1105_; uint8_t v___x_1106_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_st_ref_get(v___y_1101_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = l_Lean_Name_isAnonymous(v_declHint_1100_);
if (v___x_1106_ == 0)
{
uint8_t v_isExporting_1107_; 
v_isExporting_1107_ = lean_ctor_get_uint8(v_env_1105_, sizeof(void*)*13);
if (v_isExporting_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref(v_env_1105_);
lean_dec(v_declHint_1100_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_msg_1099_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
lean_inc_ref(v_env_1105_);
v___x_1109_ = l_Lean_Environment_setExporting(v_env_1105_, v___x_1106_);
lean_inc(v_declHint_1100_);
lean_inc_ref(v___x_1109_);
v___x_1110_ = l_Lean_Environment_contains(v___x_1109_, v_declHint_1100_, v_isExporting_1107_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_env_1105_);
lean_dec(v_declHint_1100_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_msg_1099_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_c_1117_; lean_object* v___x_1118_; 
v___x_1112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1114_ = l_Lean_Options_empty;
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1109_);
lean_ctor_set(v___x_1115_, 1, v___x_1112_);
lean_ctor_set(v___x_1115_, 2, v___x_1113_);
lean_ctor_set(v___x_1115_, 3, v___x_1114_);
lean_inc(v_declHint_1100_);
v___x_1116_ = l_Lean_MessageData_ofConstName(v_declHint_1100_, v___x_1106_);
v_c_1117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1117_, 0, v___x_1115_);
lean_ctor_set(v_c_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1105_, v_declHint_1100_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v_env_1105_);
lean_dec(v_declHint_1100_);
v___x_1119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_c_1117_);
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_MessageData_note(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_msg_1099_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1182_; 
v_val_1126_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1128_ = v___x_1118_;
v_isShared_1129_ = v_isSharedCheck_1182_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v___x_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1182_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v_modules_1131_; lean_object* v_moduleNames_1132_; lean_object* v_mod_1133_; uint8_t v___y_1135_; uint8_t v___x_1165_; 
v___x_1130_ = l_Lean_Environment_header(v_env_1105_);
lean_dec_ref(v_env_1105_);
v_modules_1131_ = lean_ctor_get(v___x_1130_, 3);
lean_inc_ref(v_modules_1131_);
v_moduleNames_1132_ = lean_ctor_get(v___x_1130_, 4);
lean_inc_ref(v_moduleNames_1132_);
lean_dec_ref(v___x_1130_);
v_mod_1133_ = lean_array_get(v___x_1103_, v_moduleNames_1132_, v_val_1126_);
lean_dec_ref(v_moduleNames_1132_);
v___x_1165_ = l_Lean_isPrivateName(v_declHint_1100_);
lean_dec(v_declHint_1100_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_array_get_size(v_modules_1131_);
v___x_1167_ = lean_nat_dec_lt(v_val_1126_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v_modules_1131_);
lean_dec(v_val_1126_);
v___y_1135_ = v___x_1165_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1168_; lean_object* v_toImport_1169_; uint8_t v_isExported_1170_; 
v___x_1168_ = lean_array_fget(v_modules_1131_, v_val_1126_);
lean_dec(v_val_1126_);
lean_dec_ref(v_modules_1131_);
v_toImport_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_toImport_1169_);
lean_dec(v___x_1168_);
v_isExported_1170_ = lean_ctor_get_uint8(v_toImport_1169_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1169_);
v___y_1135_ = v_isExported_1170_;
goto v___jp_1134_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v_modules_1131_);
lean_del_object(v___x_1128_);
lean_dec(v_val_1126_);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_c_1117_);
v___x_1173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_MessageData_ofName(v_mod_1133_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_note(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_msg_1099_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
v___jp_1134_:
{
if (v___y_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_c_1117_);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_ofName(v_mod_1133_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_note(v___x_1143_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_msg_1099_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1145_);
v___x_1147_ = v___x_1128_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v_c_1117_);
v___x_1151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_MessageData_ofName(v_mod_1133_);
lean_inc_ref(v___x_1153_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1153_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1099_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1161_);
v___x_1163_ = v___x_1128_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
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
lean_object* v___x_1183_; 
lean_dec_ref(v_env_1105_);
lean_dec(v_declHint_1100_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_msg_1099_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1184_, v_declHint_1185_, v___y_1186_);
lean_dec(v___y_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1189_, lean_object* v_declHint_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
v___x_1194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1189_, v_declHint_1190_, v___y_1192_);
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = l_Lean_unknownIdentifierMessageTag;
v___x_1200_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1205_, lean_object* v_declHint_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1205_, v_declHint_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v_declHint_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1219_; 
v___x_1217_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1212_, v_declHint_1213_, v___y_1214_, v___y_1215_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1211_, v_a_1218_, v___y_1214_, v___y_1215_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1220_, lean_object* v_msg_1221_, lean_object* v_declHint_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1220_, v_msg_1221_, v_declHint_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v_ref_1220_);
return v_res_1226_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1229_ = l_Lean_stringToMessageData(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1232_ = l_Lean_stringToMessageData(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1233_, lean_object* v_constName_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1238_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1239_ = 0;
lean_inc(v_constName_1234_);
v___x_1240_ = l_Lean_MessageData_ofConstName(v_constName_1234_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1233_, v___x_1243_, v_constName_1234_, v___y_1235_, v___y_1236_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1245_, lean_object* v_constName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1245_, v_constName_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v_ref_1245_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
if (lean_obj_tag(v_a_1251_) == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = l_List_reverse___redArg(v_a_1252_);
return v___x_1253_;
}
else
{
lean_object* v_head_1254_; lean_object* v_tail_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1266_; 
v_head_1254_ = lean_ctor_get(v_a_1251_, 0);
v_tail_1255_ = lean_ctor_get(v_a_1251_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_a_1251_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1257_ = v_a_1251_;
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_tail_1255_);
lean_inc(v_head_1254_);
lean_dec(v_a_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_snd_1259_; uint8_t v___x_1260_; 
v_snd_1259_ = lean_ctor_get(v_head_1254_, 1);
v___x_1260_ = l_List_isEmpty___redArg(v_snd_1259_);
if (v___x_1260_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_head_1254_);
v_a_1251_ = v_tail_1255_;
goto _start;
}
else
{
lean_object* v___x_1263_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_a_1252_);
v___x_1263_ = v___x_1257_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_head_1254_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1252_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_a_1251_ = v_tail_1255_;
v_a_1252_ = v___x_1263_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1267_, lean_object* v_cs_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v_cs_1273_; uint8_t v___x_1277_; 
v___x_1272_ = lean_box(0);
v_cs_1273_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1268_, v___x_1272_);
v___x_1277_ = l_List_isEmpty___redArg(v_cs_1273_);
if (v___x_1277_ == 0)
{
lean_dec(v_n_1267_);
goto v___jp_1274_;
}
else
{
lean_object* v_ref_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_cs_1273_);
v_ref_1278_ = lean_ctor_get(v___y_1269_, 2);
v___x_1279_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1278_, v_n_1267_, v___y_1269_, v___y_1270_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
v___jp_1274_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1273_, v___x_1272_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1288_, lean_object* v_cs_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1288_, v_cs_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
lean_inc(v_n_1294_);
v___x_1298_ = l_Lean_realizeGlobalName(v_n_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1294_, v_a_1299_, v_a_1295_, v_a_1296_);
return v___x_1300_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_n_1294_);
v_a_1301_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1298_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1298_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_realizeGlobalConstCore(v_n_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1314_, lean_object* v_ref_1315_, lean_object* v_constName_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1315_, v_constName_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v_constName_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1321_, v_ref_1322_, v_constName_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v_ref_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1328_, lean_object* v_ref_1329_, lean_object* v_msg_1330_, lean_object* v_declHint_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1329_, v_msg_1330_, v_declHint_1331_, v___y_1332_, v___y_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_ref_1337_, lean_object* v_msg_1338_, lean_object* v_declHint_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1336_, v_ref_1337_, v_msg_1338_, v_declHint_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v_ref_1337_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1344_, lean_object* v_declHint_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1344_, v_declHint_1345_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1350_, lean_object* v_declHint_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1350_, v_declHint_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1356_, lean_object* v_ref_1357_, lean_object* v_msg_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1357_, v_msg_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1363_, v_ref_1364_, v_msg_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v_ref_1364_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1370_, lean_object* v_msg_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1371_, v___y_1372_, v___y_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1376_, v_msg_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
if (lean_obj_tag(v_a_1382_) == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_List_reverse___redArg(v_a_1383_);
return v___x_1384_;
}
else
{
lean_object* v_head_1385_; lean_object* v_tail_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1395_; 
v_head_1385_ = lean_ctor_get(v_a_1382_, 0);
v_tail_1386_ = lean_ctor_get(v_a_1382_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_a_1382_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1388_ = v_a_1382_;
v_isShared_1389_ = v_isSharedCheck_1395_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_tail_1386_);
lean_inc(v_head_1385_);
lean_dec(v_a_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1395_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = l_Lean_MessageData_ofExpr(v_head_1385_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_a_1383_);
lean_ctor_set(v___x_1388_, 0, v___x_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_a_1383_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v_a_1382_ = v_tail_1386_;
v_a_1383_ = v___x_1392_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = l_List_reverse___redArg(v_a_1397_);
return v___x_1398_;
}
else
{
lean_object* v_head_1399_; lean_object* v_tail_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1410_; 
v_head_1399_ = lean_ctor_get(v_a_1396_, 0);
v_tail_1400_ = lean_ctor_get(v_a_1396_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1402_ = v_a_1396_;
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_tail_1400_);
lean_inc(v_head_1399_);
lean_dec(v_a_1396_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_mkConst(v_head_1399_, v___x_1404_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v_a_1397_);
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1397_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
v_a_1396_ = v_tail_1400_;
v_a_1397_ = v___x_1407_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1416_ = l_Lean_stringToMessageData(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1417_, lean_object* v_cs_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
if (lean_obj_tag(v_cs_1418_) == 1)
{
lean_object* v_tail_1434_; 
v_tail_1434_ = lean_ctor_get(v_cs_1418_, 1);
if (lean_obj_tag(v_tail_1434_) == 0)
{
lean_object* v_head_1435_; lean_object* v___x_1436_; 
lean_dec(v_n_1417_);
v_head_1435_ = lean_ctor_get(v_cs_1418_, 0);
lean_inc(v_head_1435_);
lean_dec_ref_known(v_cs_1418_, 2);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_head_1435_);
return v___x_1436_;
}
else
{
goto v___jp_1422_;
}
}
else
{
goto v___jp_1422_;
}
v___jp_1422_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1423_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1424_ = l_Lean_MessageData_ofName(v_n_1417_);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_box(0);
v___x_1429_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1418_, v___x_1428_);
v___x_1430_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1429_, v___x_1428_);
v___x_1431_ = l_Lean_MessageData_ofList(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1427_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1432_, v___y_1419_, v___y_1420_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1437_, lean_object* v_cs_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1437_, v_cs_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; 
lean_inc(v_n_1443_);
v___x_1447_ = l_Lean_realizeGlobalConstCore(v_n_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1443_, v_a_1448_, v_a_1444_, v_a_1445_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_n_1443_);
v_a_1450_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1447_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1447_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
if (lean_obj_tag(v_a_1463_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_array_to_list(v_a_1464_);
return v___x_1465_;
}
else
{
lean_object* v_head_1466_; 
v_head_1466_ = lean_ctor_get(v_a_1463_, 0);
if (lean_obj_tag(v_head_1466_) == 1)
{
lean_object* v_fields_1467_; 
v_fields_1467_ = lean_ctor_get(v_head_1466_, 1);
if (lean_obj_tag(v_fields_1467_) == 0)
{
lean_object* v_tail_1468_; lean_object* v_n_1469_; lean_object* v___x_1470_; 
lean_inc_ref(v_head_1466_);
v_tail_1468_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_tail_1468_);
lean_dec_ref_known(v_a_1463_, 2);
v_n_1469_ = lean_ctor_get(v_head_1466_, 0);
lean_inc(v_n_1469_);
lean_dec_ref_known(v_head_1466_, 2);
v___x_1470_ = lean_array_push(v_a_1464_, v_n_1469_);
v_a_1463_ = v_tail_1468_;
v_a_1464_ = v___x_1470_;
goto _start;
}
else
{
lean_object* v_tail_1472_; 
v_tail_1472_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_tail_1472_);
lean_dec_ref_known(v_a_1463_, 2);
v_a_1463_ = v_tail_1472_;
goto _start;
}
}
else
{
lean_object* v_tail_1474_; 
v_tail_1474_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_tail_1474_);
lean_dec_ref_known(v_a_1463_, 2);
v_a_1463_ = v_tail_1474_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1482_ = l_Lean_MessageData_ofFormat(v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1483_, lean_object* v_k_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
if (lean_obj_tag(v_stx_1483_) == 3)
{
lean_object* v_val_1488_; lean_object* v_preresolved_1489_; lean_object* v___x_1490_; lean_object* v_pre_1491_; uint8_t v___x_1492_; 
v_val_1488_ = lean_ctor_get(v_stx_1483_, 2);
lean_inc(v_val_1488_);
v_preresolved_1489_ = lean_ctor_get(v_stx_1483_, 3);
v___x_1490_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1489_);
v_pre_1491_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1489_, v___x_1490_);
v___x_1492_ = l_List_isEmpty___redArg(v_pre_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec(v_val_1488_);
lean_dec_ref_known(v_stx_1483_, 4);
lean_dec_ref(v_k_1484_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_pre_1491_);
return v___x_1493_;
}
else
{
lean_object* v_toCold_1494_; lean_object* v_currRecDepth_1495_; lean_object* v_ref_1496_; uint16_t v_optionFlags_1497_; uint8_t v_suppressElabErrors_1498_; uint8_t v_isRecordingDeps_1499_; lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_pre_1491_);
v_toCold_1494_ = lean_ctor_get(v___y_1485_, 0);
v_currRecDepth_1495_ = lean_ctor_get(v___y_1485_, 1);
v_ref_1496_ = lean_ctor_get(v___y_1485_, 2);
v_optionFlags_1497_ = lean_ctor_get_uint16(v___y_1485_, sizeof(void*)*3);
v_suppressElabErrors_1498_ = lean_ctor_get_uint8(v___y_1485_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1499_ = lean_ctor_get_uint8(v___y_1485_, sizeof(void*)*3 + 3);
v_ref_1500_ = l_Lean_replaceRef(v_stx_1483_, v_ref_1496_);
lean_dec_ref_known(v_stx_1483_, 4);
lean_inc(v_currRecDepth_1495_);
lean_inc_ref(v_toCold_1494_);
v___x_1501_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1501_, 0, v_toCold_1494_);
lean_ctor_set(v___x_1501_, 1, v_currRecDepth_1495_);
lean_ctor_set(v___x_1501_, 2, v_ref_1500_);
lean_ctor_set_uint16(v___x_1501_, sizeof(void*)*3, v_optionFlags_1497_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*3 + 2, v_suppressElabErrors_1498_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*3 + 3, v_isRecordingDeps_1499_);
lean_inc(v___y_1486_);
v___x_1502_ = lean_apply_4(v_k_1484_, v_val_1488_, v___x_1501_, v___y_1486_, lean_box(0));
return v___x_1502_;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_k_1484_);
v___x_1503_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1504_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1483_, v___x_1503_, v___y_1485_, v___y_1486_);
lean_dec(v_stx_1483_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1505_, lean_object* v_k_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1505_, v_k_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_toCold_1516_; lean_object* v_currRecDepth_1517_; lean_object* v_ref_1518_; uint16_t v_optionFlags_1519_; uint8_t v_suppressElabErrors_1520_; uint8_t v_isRecordingDeps_1521_; lean_object* v___x_1522_; lean_object* v_ref_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_toCold_1516_ = lean_ctor_get(v_a_1513_, 0);
v_currRecDepth_1517_ = lean_ctor_get(v_a_1513_, 1);
v_ref_1518_ = lean_ctor_get(v_a_1513_, 2);
v_optionFlags_1519_ = lean_ctor_get_uint16(v_a_1513_, sizeof(void*)*3);
v_suppressElabErrors_1520_ = lean_ctor_get_uint8(v_a_1513_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1521_ = lean_ctor_get_uint8(v_a_1513_, sizeof(void*)*3 + 3);
v___x_1522_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1523_ = l_Lean_replaceRef(v_stx_1512_, v_ref_1518_);
lean_inc(v_currRecDepth_1517_);
lean_inc_ref(v_toCold_1516_);
v___x_1524_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1524_, 0, v_toCold_1516_);
lean_ctor_set(v___x_1524_, 1, v_currRecDepth_1517_);
lean_ctor_set(v___x_1524_, 2, v_ref_1523_);
lean_ctor_set_uint16(v___x_1524_, sizeof(void*)*3, v_optionFlags_1519_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*3 + 2, v_suppressElabErrors_1520_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*3 + 3, v_isRecordingDeps_1521_);
v___x_1525_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1512_, v___x_1522_, v___x_1524_, v_a_1514_);
lean_dec_ref_known(v___x_1524_, 3);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_realizeGlobalConst(v_stx_1526_, v_a_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1530_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_instMonadEIO___redArg();
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_toApplicative_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1571_; 
v___x_1538_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1539_ = l_StateRefT_x27_instMonad___redArg(v___x_1538_);
v_toApplicative_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1539_, 1);
lean_dec(v_unused_1572_);
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1571_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_toApplicative_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1571_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_toFunctor_1544_; lean_object* v_toSeq_1545_; lean_object* v_toSeqLeft_1546_; lean_object* v_toSeqRight_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1569_; 
v_toFunctor_1544_ = lean_ctor_get(v_toApplicative_1540_, 0);
v_toSeq_1545_ = lean_ctor_get(v_toApplicative_1540_, 2);
v_toSeqLeft_1546_ = lean_ctor_get(v_toApplicative_1540_, 3);
v_toSeqRight_1547_ = lean_ctor_get(v_toApplicative_1540_, 4);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_toApplicative_1540_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_toApplicative_1540_, 1);
lean_dec(v_unused_1570_);
v___x_1549_ = v_toApplicative_1540_;
v_isShared_1550_ = v_isSharedCheck_1569_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_toSeqRight_1547_);
lean_inc(v_toSeqLeft_1546_);
lean_inc(v_toSeq_1545_);
lean_inc(v_toFunctor_1544_);
lean_dec(v_toApplicative_1540_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1569_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1560_; 
v___f_1551_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1552_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1544_);
v___f_1553_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1553_, 0, v_toFunctor_1544_);
v___f_1554_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1554_, 0, v_toFunctor_1544_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___f_1553_);
lean_ctor_set(v___x_1555_, 1, v___f_1554_);
v___f_1556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1556_, 0, v_toSeqRight_1547_);
v___f_1557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1557_, 0, v_toSeqLeft_1546_);
v___f_1558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1558_, 0, v_toSeq_1545_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 4, v___f_1556_);
lean_ctor_set(v___x_1549_, 3, v___f_1557_);
lean_ctor_set(v___x_1549_, 2, v___f_1558_);
lean_ctor_set(v___x_1549_, 1, v___f_1551_);
lean_ctor_set(v___x_1549_, 0, v___x_1555_);
v___x_1560_ = v___x_1549_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___f_1551_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v___f_1558_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v___f_1557_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v___f_1556_);
v___x_1560_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___f_1552_);
lean_ctor_set(v___x_1542_, 0, v___x_1560_);
v___x_1562_ = v___x_1542_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___f_1552_);
v___x_1562_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_195__overap_1565_; lean_object* v___x_1566_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = l_instInhabitedOfMonad___redArg(v___x_1562_, v___x_1563_);
v___x_195__overap_1565_ = lean_panic_fn_borrowed(v___x_1564_, v_msg_1534_);
lean_dec(v___x_1564_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
v___x_1566_ = lean_apply_3(v___x_195__overap_1565_, v___y_1535_, v___y_1536_, lean_box(0));
return v___x_1566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1579_, lean_object* v_x_1580_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
return v_x_1579_;
}
else
{
lean_object* v_head_1581_; lean_object* v_tail_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_head_1581_ = lean_ctor_get(v_x_1580_, 0);
v_tail_1582_ = lean_ctor_get(v_x_1580_, 1);
v___x_1583_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1584_ = lean_string_append(v_x_1579_, v___x_1583_);
v___x_1585_ = lean_expr_dbg_to_string(v_head_1581_);
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
lean_dec_ref(v___x_1585_);
v_x_1579_ = v___x_1586_;
v_x_1580_ = v_tail_1582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1588_, v_x_1589_);
lean_dec(v_x_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1595_;
}
else
{
lean_object* v_tail_1596_; 
v_tail_1596_ = lean_ctor_get(v_x_1594_, 1);
if (lean_obj_tag(v_tail_1596_) == 0)
{
lean_object* v_head_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_head_1597_ = lean_ctor_get(v_x_1594_, 0);
v___x_1598_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1599_ = lean_expr_dbg_to_string(v_head_1597_);
v___x_1600_ = lean_string_append(v___x_1598_, v___x_1599_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
return v___x_1602_;
}
else
{
lean_object* v_head_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint32_t v___x_1608_; lean_object* v___x_1609_; 
v_head_1603_ = lean_ctor_get(v_x_1594_, 0);
v___x_1604_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1605_ = lean_expr_dbg_to_string(v_head_1603_);
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1606_, v_tail_1596_);
v___x_1608_ = 93;
v___x_1609_ = lean_string_push(v___x_1607_, v___x_1608_);
return v___x_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1610_);
lean_dec(v_x_1610_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1616_ = lean_unsigned_to_nat(11u);
v___x_1617_ = lean_unsigned_to_nat(429u);
v___x_1618_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1619_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1623_, lean_object* v_cs_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
if (lean_obj_tag(v_cs_1624_) == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_id_1623_);
v___x_1628_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1629_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1628_, v___y_1625_, v___y_1626_);
return v___x_1629_;
}
else
{
lean_object* v_tail_1630_; 
v_tail_1630_ = lean_ctor_get(v_cs_1624_, 1);
if (lean_obj_tag(v_tail_1630_) == 0)
{
lean_object* v_head_1631_; lean_object* v___x_1632_; 
lean_dec(v_id_1623_);
v_head_1631_ = lean_ctor_get(v_cs_1624_, 0);
lean_inc(v_head_1631_);
lean_dec_ref_known(v_cs_1624_, 2);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_head_1631_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1633_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1634_ = lean_box(0);
v___x_1635_ = 0;
lean_inc(v_id_1623_);
v___x_1636_ = l_Lean_Syntax_formatStx(v_id_1623_, v___x_1634_, v___x_1635_);
v___x_1637_ = l_Std_Format_defWidth;
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = l_Std_Format_pretty(v___x_1636_, v___x_1637_, v___x_1638_, v___x_1638_);
v___x_1640_ = lean_string_append(v___x_1633_, v___x_1639_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1642_ = lean_string_append(v___x_1640_, v___x_1641_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1624_, v___x_1643_);
v___x_1645_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1644_);
lean_dec(v___x_1644_);
v___x_1646_ = lean_string_append(v___x_1642_, v___x_1645_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
v___x_1648_ = l_Lean_MessageData_ofFormat(v___x_1647_);
v___x_1649_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1623_, v___x_1648_, v___y_1625_, v___y_1626_);
lean_dec(v_id_1623_);
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1650_, lean_object* v_cs_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1650_, v_cs_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; 
lean_inc(v_id_1656_);
v___x_1660_ = l_Lean_realizeGlobalConst(v_id_1656_, v_a_1657_, v_a_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1656_, v_a_1661_, v_a_1657_, v_a_1658_);
return v___x_1662_;
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_id_1656_);
v_a_1663_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1660_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1660_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_realizeGlobalConstNoOverload(v_id_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1675_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_unsigned_to_nat(3863082579u);
v___x_1708_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1709_ = l_Lean_Name_num___override(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1712_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1713_ = l_Lean_Name_str___override(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1716_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1717_ = l_Lean_Name_str___override(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_unsigned_to_nat(2u);
v___x_1719_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1720_ = l_Lean_Name_num___override(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1723_ = 0;
v___x_1724_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1725_ = l_Lean_registerTraceClass(v___x_1722_, v___x_1723_, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1727_;
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

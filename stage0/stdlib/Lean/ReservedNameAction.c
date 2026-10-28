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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_toCold_188_; lean_object* v_currRecDepth_189_; lean_object* v_ref_190_; uint16_t v_optionFlags_191_; uint8_t v_suppressElabErrors_192_; uint8_t v_checkDeprecated_193_; uint8_t v_isRecordingDeps_194_; lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_traceState_198_; lean_object* v_traces_199_; lean_object* v___x_200_; size_t v_sz_201_; size_t v___x_202_; lean_object* v___x_203_; lean_object* v_msg_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_244_; 
v_toCold_188_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_189_ = lean_ctor_get(v___y_185_, 1);
v_ref_190_ = lean_ctor_get(v___y_185_, 2);
v_optionFlags_191_ = lean_ctor_get_uint16(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_192_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 2);
v_checkDeprecated_193_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 3);
v_isRecordingDeps_194_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 4);
v_ref_195_ = l_Lean_replaceRef(v_ref_183_, v_ref_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_toCold_188_);
v___x_196_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_196_, 0, v_toCold_188_);
lean_ctor_set(v___x_196_, 1, v_currRecDepth_189_);
lean_ctor_set(v___x_196_, 2, v_ref_195_);
lean_ctor_set_uint16(v___x_196_, sizeof(void*)*3, v_optionFlags_191_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 2, v_suppressElabErrors_192_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 3, v_checkDeprecated_193_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 4, v_isRecordingDeps_194_);
v___x_197_ = lean_st_ref_get(v___y_186_);
v_traceState_198_ = lean_ctor_get(v___x_197_, 4);
lean_inc_ref(v_traceState_198_);
lean_dec(v___x_197_);
v_traces_199_ = lean_ctor_get(v_traceState_198_, 0);
lean_inc_ref(v_traces_199_);
lean_dec_ref(v_traceState_198_);
v___x_200_ = l_Lean_PersistentArray_toArray___redArg(v_traces_199_);
lean_dec_ref(v_traces_199_);
v_sz_201_ = lean_array_size(v___x_200_);
v___x_202_ = ((size_t)0ULL);
v___x_203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_201_, v___x_202_, v___x_200_);
v_msg_204_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_204_, 0, v_data_182_);
lean_ctor_set(v_msg_204_, 1, v_msg_184_);
lean_ctor_set(v_msg_204_, 2, v___x_203_);
v___x_205_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_204_, v___x_196_, v___y_186_);
lean_dec_ref_known(v___x_196_, 3);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_244_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_244_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_244_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v_traceState_211_; lean_object* v_env_212_; lean_object* v_nextMacroScope_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_cache_216_; lean_object* v_recordedDeps_217_; lean_object* v_messages_218_; lean_object* v_infoState_219_; lean_object* v_snapshotTasks_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_243_; 
v___x_210_ = lean_st_ref_take(v___y_186_);
v_traceState_211_ = lean_ctor_get(v___x_210_, 4);
v_env_212_ = lean_ctor_get(v___x_210_, 0);
v_nextMacroScope_213_ = lean_ctor_get(v___x_210_, 1);
v_ngen_214_ = lean_ctor_get(v___x_210_, 2);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_210_, 3);
v_cache_216_ = lean_ctor_get(v___x_210_, 5);
v_recordedDeps_217_ = lean_ctor_get(v___x_210_, 6);
v_messages_218_ = lean_ctor_get(v___x_210_, 7);
v_infoState_219_ = lean_ctor_get(v___x_210_, 8);
v_snapshotTasks_220_ = lean_ctor_get(v___x_210_, 9);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_243_ == 0)
{
v___x_222_ = v___x_210_;
v_isShared_223_ = v_isSharedCheck_243_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snapshotTasks_220_);
lean_inc(v_infoState_219_);
lean_inc(v_messages_218_);
lean_inc(v_recordedDeps_217_);
lean_inc(v_cache_216_);
lean_inc(v_traceState_211_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_nextMacroScope_213_);
lean_inc(v_env_212_);
lean_dec(v___x_210_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_243_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint64_t v_tid_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_241_; 
v_tid_224_ = lean_ctor_get_uint64(v_traceState_211_, sizeof(void*)*1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_traceState_211_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_traceState_211_, 0);
lean_dec(v_unused_242_);
v___x_226_ = v_traceState_211_;
v_isShared_227_ = v_isSharedCheck_241_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_traceState_211_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_241_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_ref_183_);
lean_ctor_set(v___x_229_, 1, v_a_206_);
v___x_230_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_181_, v___x_229_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_230_);
v___x_232_ = v___x_226_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_230_);
lean_ctor_set_uint64(v_reuseFailAlloc_240_, sizeof(void*)*1, v_tid_224_);
v___x_232_ = v_reuseFailAlloc_240_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 4, v___x_232_);
v___x_234_ = v___x_222_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_env_212_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_nextMacroScope_213_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v_cache_216_);
lean_ctor_set(v_reuseFailAlloc_239_, 6, v_recordedDeps_217_);
lean_ctor_set(v_reuseFailAlloc_239_, 7, v_messages_218_);
lean_ctor_set(v_reuseFailAlloc_239_, 8, v_infoState_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 9, v_snapshotTasks_220_);
v___x_234_ = v_reuseFailAlloc_239_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_st_ref_put(v___y_186_, v___x_234_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_228_);
v___x_237_ = v___x_208_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_228_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_245_, lean_object* v_data_246_, lean_object* v_ref_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_245_, v_data_246_, v_ref_247_, v_msg_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v_x_253_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v_x_253_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v_x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v_x_253_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v_x_253_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v_x_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_271_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_274_){
_start:
{
if (lean_obj_tag(v_e_274_) == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 2;
return v___x_275_;
}
else
{
lean_object* v_a_276_; uint8_t v___x_277_; 
v_a_276_ = lean_ctor_get(v_e_274_, 0);
v___x_277_ = lean_unbox(v_a_276_);
if (v___x_277_ == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 1;
return v___x_278_;
}
else
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_280_);
lean_dec_ref(v_e_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_283_; double v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_float_of_nat(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_288_; double v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1000u);
v___x_289_ = lean_float_of_nat(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_290_, uint8_t v_collapsed_291_, lean_object* v_tag_292_, lean_object* v_opts_293_, uint8_t v_clsEnabled_294_, lean_object* v_oldTraces_295_, lean_object* v_msg_296_, lean_object* v_resStartStop_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v_data_306_; lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___y_322_; lean_object* v_a_323_; uint8_t v___y_338_; double v___y_370_; 
v_fst_301_ = lean_ctor_get(v_resStartStop_297_, 0);
lean_inc(v_fst_301_);
v_snd_302_ = lean_ctor_get(v_resStartStop_297_, 1);
lean_inc(v_snd_302_);
lean_dec_ref(v_resStartStop_297_);
v_fst_317_ = lean_ctor_get(v_snd_302_, 0);
lean_inc(v_fst_317_);
v_snd_318_ = lean_ctor_get(v_snd_302_, 1);
lean_inc(v_snd_318_);
lean_dec(v_snd_302_);
v___x_319_ = l_Lean_trace_profiler;
v___x_320_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_293_, v___x_319_);
if (v___x_320_ == 0)
{
v___y_338_ = v___x_320_;
goto v___jp_337_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_trace_profiler_useHeartbeats;
v___x_376_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_293_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; double v___x_379_; double v___x_380_; double v___x_381_; 
v___x_377_ = l_Lean_trace_profiler_threshold;
v___x_378_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_293_, v___x_377_);
v___x_379_ = lean_float_of_nat(v___x_378_);
v___x_380_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_381_ = lean_float_div(v___x_379_, v___x_380_);
v___y_370_ = v___x_381_;
goto v___jp_369_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; double v___x_384_; 
v___x_382_ = l_Lean_trace_profiler_threshold;
v___x_383_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_293_, v___x_382_);
v___x_384_ = lean_float_of_nat(v___x_383_);
v___y_370_ = v___x_384_;
goto v___jp_369_;
}
}
v___jp_303_:
{
lean_object* v___x_307_; 
lean_inc(v___y_304_);
v___x_307_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_295_, v_data_306_, v___y_304_, v___y_305_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_301_);
return v___x_308_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_fst_301_);
v_a_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
v___jp_321_:
{
uint8_t v_result_324_; lean_object* v___x_325_; lean_object* v___x_326_; double v___x_327_; lean_object* v_data_328_; 
v_result_324_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_301_);
v___x_325_ = lean_box(v_result_324_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___x_327_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
lean_inc_ref(v_tag_292_);
lean_inc_ref(v___x_326_);
lean_inc(v_cls_290_);
v_data_328_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_328_, 0, v_cls_290_);
lean_ctor_set(v_data_328_, 1, v___x_326_);
lean_ctor_set(v_data_328_, 2, v_tag_292_);
lean_ctor_set_float(v_data_328_, sizeof(void*)*3, v___x_327_);
lean_ctor_set_float(v_data_328_, sizeof(void*)*3 + 8, v___x_327_);
lean_ctor_set_uint8(v_data_328_, sizeof(void*)*3 + 16, v_collapsed_291_);
if (v___x_320_ == 0)
{
lean_dec_ref_known(v___x_326_, 1);
lean_dec(v_snd_318_);
lean_dec(v_fst_317_);
lean_dec_ref(v_tag_292_);
lean_dec(v_cls_290_);
v___y_304_ = v___y_322_;
v___y_305_ = v_a_323_;
v_data_306_ = v_data_328_;
goto v___jp_303_;
}
else
{
lean_object* v_data_329_; double v___x_330_; double v___x_331_; 
lean_dec_ref_known(v_data_328_, 3);
v_data_329_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_329_, 0, v_cls_290_);
lean_ctor_set(v_data_329_, 1, v___x_326_);
lean_ctor_set(v_data_329_, 2, v_tag_292_);
v___x_330_ = lean_unbox_float(v_fst_317_);
lean_dec(v_fst_317_);
lean_ctor_set_float(v_data_329_, sizeof(void*)*3, v___x_330_);
v___x_331_ = lean_unbox_float(v_snd_318_);
lean_dec(v_snd_318_);
lean_ctor_set_float(v_data_329_, sizeof(void*)*3 + 8, v___x_331_);
lean_ctor_set_uint8(v_data_329_, sizeof(void*)*3 + 16, v_collapsed_291_);
v___y_304_ = v___y_322_;
v___y_305_ = v_a_323_;
v_data_306_ = v_data_329_;
goto v___jp_303_;
}
}
v___jp_332_:
{
lean_object* v_ref_333_; lean_object* v___x_334_; 
v_ref_333_ = lean_ctor_get(v___y_298_, 2);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v_fst_301_);
v___x_334_ = lean_apply_4(v_msg_296_, v_fst_301_, v___y_298_, v___y_299_, lean_box(0));
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___y_322_ = v_ref_333_;
v_a_323_ = v_a_335_;
goto v___jp_321_;
}
else
{
lean_object* v___x_336_; 
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
v___y_322_ = v_ref_333_;
v_a_323_ = v___x_336_;
goto v___jp_321_;
}
}
v___jp_337_:
{
if (v_clsEnabled_294_ == 0)
{
if (v___y_338_ == 0)
{
lean_object* v___x_339_; lean_object* v_traceState_340_; lean_object* v_env_341_; lean_object* v_nextMacroScope_342_; lean_object* v_ngen_343_; lean_object* v_auxDeclNGen_344_; lean_object* v_cache_345_; lean_object* v_recordedDeps_346_; lean_object* v_messages_347_; lean_object* v_infoState_348_; lean_object* v_snapshotTasks_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_snd_318_);
lean_dec(v_fst_317_);
lean_dec_ref(v_msg_296_);
lean_dec_ref(v_tag_292_);
lean_dec(v_cls_290_);
v___x_339_ = lean_st_ref_take(v___y_299_);
v_traceState_340_ = lean_ctor_get(v___x_339_, 4);
v_env_341_ = lean_ctor_get(v___x_339_, 0);
v_nextMacroScope_342_ = lean_ctor_get(v___x_339_, 1);
v_ngen_343_ = lean_ctor_get(v___x_339_, 2);
v_auxDeclNGen_344_ = lean_ctor_get(v___x_339_, 3);
v_cache_345_ = lean_ctor_get(v___x_339_, 5);
v_recordedDeps_346_ = lean_ctor_get(v___x_339_, 6);
v_messages_347_ = lean_ctor_get(v___x_339_, 7);
v_infoState_348_ = lean_ctor_get(v___x_339_, 8);
v_snapshotTasks_349_ = lean_ctor_get(v___x_339_, 9);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_368_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snapshotTasks_349_);
lean_inc(v_infoState_348_);
lean_inc(v_messages_347_);
lean_inc(v_recordedDeps_346_);
lean_inc(v_cache_345_);
lean_inc(v_traceState_340_);
lean_inc(v_auxDeclNGen_344_);
lean_inc(v_ngen_343_);
lean_inc(v_nextMacroScope_342_);
lean_inc(v_env_341_);
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_368_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
uint64_t v_tid_353_; lean_object* v_traces_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_367_; 
v_tid_353_ = lean_ctor_get_uint64(v_traceState_340_, sizeof(void*)*1);
v_traces_354_ = lean_ctor_get(v_traceState_340_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_traceState_340_);
if (v_isSharedCheck_367_ == 0)
{
v___x_356_ = v_traceState_340_;
v_isShared_357_ = v_isSharedCheck_367_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_traces_354_);
lean_dec(v_traceState_340_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_367_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_358_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_295_, v_traces_354_);
lean_dec_ref(v_traces_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_358_);
v___x_360_ = v___x_356_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_358_);
lean_ctor_set_uint64(v_reuseFailAlloc_366_, sizeof(void*)*1, v_tid_353_);
v___x_360_ = v_reuseFailAlloc_366_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 4, v___x_360_);
v___x_362_ = v___x_351_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_env_341_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_nextMacroScope_342_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_ngen_343_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_auxDeclNGen_344_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_365_, 5, v_cache_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 6, v_recordedDeps_346_);
lean_ctor_set(v_reuseFailAlloc_365_, 7, v_messages_347_);
lean_ctor_set(v_reuseFailAlloc_365_, 8, v_infoState_348_);
lean_ctor_set(v_reuseFailAlloc_365_, 9, v_snapshotTasks_349_);
v___x_362_ = v_reuseFailAlloc_365_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_st_ref_put(v___y_299_, v___x_362_);
v___x_364_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_301_);
return v___x_364_;
}
}
}
}
}
else
{
goto v___jp_332_;
}
}
else
{
goto v___jp_332_;
}
}
v___jp_369_:
{
double v___x_371_; double v___x_372_; double v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_unbox_float(v_snd_318_);
v___x_372_ = lean_unbox_float(v_fst_317_);
v___x_373_ = lean_float_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_float_decLt(v___y_370_, v___x_373_);
v___y_338_ = v___x_374_;
goto v___jp_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_385_, lean_object* v_collapsed_386_, lean_object* v_tag_387_, lean_object* v_opts_388_, lean_object* v_clsEnabled_389_, lean_object* v_oldTraces_390_, lean_object* v_msg_391_, lean_object* v_resStartStop_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_collapsed_boxed_396_; uint8_t v_clsEnabled_boxed_397_; lean_object* v_res_398_; 
v_collapsed_boxed_396_ = lean_unbox(v_collapsed_386_);
v_clsEnabled_boxed_397_ = lean_unbox(v_clsEnabled_389_);
v_res_398_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_385_, v_collapsed_boxed_396_, v_tag_387_, v_opts_388_, v_clsEnabled_boxed_397_, v_oldTraces_390_, v_msg_391_, v_resStartStop_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_opts_388_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_399_, lean_object* v_as_400_, size_t v_i_401_, size_t v_stop_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_eq(v_i_401_, v_stop_402_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; lean_object* v___x_5263__overap_408_; lean_object* v___x_409_; 
v___x_407_ = 1;
v___x_5263__overap_408_ = lean_array_uget_borrowed(v_as_400_, v_i_401_);
lean_inc(v___x_5263__overap_408_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v_name_399_);
v___x_409_ = lean_apply_4(v___x_5263__overap_408_, v_name_399_, v___y_403_, v___y_404_, lean_box(0));
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; 
v___x_414_ = lean_unbox(v_a_410_);
lean_dec(v_a_410_);
if (v___x_414_ == 0)
{
size_t v___x_415_; size_t v___x_416_; 
lean_del_object(v___x_412_);
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_401_, v___x_415_);
v_i_401_ = v___x_416_;
goto _start;
}
else
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_name_399_);
v___x_418_ = lean_box(v___x_407_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_dec(v_name_399_);
return v___x_409_;
}
}
else
{
uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_name_399_);
v___x_423_ = 0;
v___x_424_ = lean_box(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_426_, lean_object* v_as_427_, lean_object* v_i_428_, lean_object* v_stop_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
size_t v_i_boxed_433_; size_t v_stop_boxed_434_; lean_object* v_res_435_; 
v_i_boxed_433_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_stop_boxed_434_ = lean_unbox_usize(v_stop_429_);
lean_dec(v_stop_429_);
v_res_435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_426_, v_as_427_, v_i_boxed_433_, v_stop_boxed_434_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec_ref(v_as_427_);
return v_res_435_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_444_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_445_ = l_Lean_Name_append(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_446_; double v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(1000000000u);
v___x_447_ = lean_float_of_nat(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_toCold_452_; lean_object* v_options_453_; lean_object* v_inheritedTraceOptions_454_; uint8_t v_hasTrace_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___y_459_; 
v_toCold_452_ = lean_ctor_get(v_a_449_, 0);
v_options_453_ = lean_ctor_get(v_toCold_452_, 2);
v_inheritedTraceOptions_454_ = lean_ctor_get(v_toCold_452_, 11);
v_hasTrace_455_ = lean_ctor_get_uint8(v_options_453_, sizeof(void*)*1);
v___x_456_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_457_ = lean_box(0);
if (v_hasTrace_455_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_st_ref_get(v___x_456_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_array_get_size(v___x_476_);
v___x_479_ = lean_nat_dec_lt(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec(v___x_476_);
lean_dec(v_name_448_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_457_);
return v___x_480_;
}
else
{
if (v___x_479_ == 0)
{
lean_object* v___x_481_; 
lean_dec(v___x_476_);
lean_dec(v_name_448_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_457_);
return v___x_481_;
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_478_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_476_, v___x_482_, v___x_483_, v_a_449_, v_a_450_);
lean_dec(v___x_476_);
v___y_459_ = v___x_484_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_a_493_; lean_object* v___y_506_; lean_object* v___y_507_; uint8_t v_a_508_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v_a_514_; lean_object* v___y_524_; lean_object* v___y_525_; uint8_t v_a_526_; 
lean_inc(v_name_448_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_485_, 0, v_name_448_);
v___x_486_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_487_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_488_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_454_, v_options_453_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = l_Lean_trace_profiler;
v___x_571_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_453_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
lean_dec_ref(v___f_485_);
v___x_572_ = lean_st_ref_get(v___x_456_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_array_get_size(v___x_572_);
v___x_575_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_572_);
lean_dec(v_name_448_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_457_);
return v___x_576_;
}
else
{
if (v___x_575_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___x_572_);
lean_dec(v_name_448_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_457_);
return v___x_577_;
}
else
{
size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_574_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_572_, v___x_578_, v___x_579_, v_a_449_, v_a_450_);
lean_dec(v___x_572_);
v___y_459_ = v___x_580_;
goto v___jp_458_;
}
}
}
else
{
goto v___jp_529_;
}
}
else
{
goto v___jp_529_;
}
v___jp_490_:
{
lean_object* v___x_494_; double v___x_495_; double v___x_496_; double v___x_497_; double v___x_498_; double v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_494_ = lean_io_mono_nanos_now();
v___x_495_ = lean_float_of_nat(v___y_492_);
v___x_496_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_497_ = lean_float_div(v___x_495_, v___x_496_);
v___x_498_ = lean_float_of_nat(v___x_494_);
v___x_499_ = lean_float_div(v___x_498_, v___x_496_);
v___x_500_ = lean_box_float(v___x_497_);
v___x_501_ = lean_box_float(v___x_499_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_a_493_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_486_, v_hasTrace_455_, v___x_487_, v_options_453_, v___x_489_, v___y_491_, v___f_485_, v___x_503_, v_a_449_, v_a_450_);
v___y_459_ = v___x_504_;
goto v___jp_458_;
}
v___jp_505_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_box(v_a_508_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___y_491_ = v___y_506_;
v___y_492_ = v___y_507_;
v_a_493_ = v___x_510_;
goto v___jp_490_;
}
v___jp_511_:
{
lean_object* v___x_515_; double v___x_516_; double v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_515_ = lean_io_get_num_heartbeats();
v___x_516_ = lean_float_of_nat(v___y_512_);
v___x_517_ = lean_float_of_nat(v___x_515_);
v___x_518_ = lean_box_float(v___x_516_);
v___x_519_ = lean_box_float(v___x_517_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_a_514_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_486_, v_hasTrace_455_, v___x_487_, v_options_453_, v___x_489_, v___y_513_, v___f_485_, v___x_521_, v_a_449_, v_a_450_);
v___y_459_ = v___x_522_;
goto v___jp_458_;
}
v___jp_523_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_box(v_a_526_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___y_512_ = v___y_524_;
v___y_513_ = v___y_525_;
v_a_514_ = v___x_528_;
goto v___jp_511_;
}
v___jp_529_:
{
lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_530_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_450_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_trace_profiler_useHeartbeats;
v___x_533_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_453_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_534_ = lean_io_mono_nanos_now();
v___x_535_ = lean_st_ref_get(v___x_456_);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_array_get_size(v___x_535_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v___x_535_);
lean_dec(v_name_448_);
v___y_506_ = v_a_531_;
v___y_507_ = v___x_534_;
v_a_508_ = v___x_538_;
goto v___jp_505_;
}
else
{
if (v___x_538_ == 0)
{
lean_dec(v___x_535_);
lean_dec(v_name_448_);
v___y_506_ = v_a_531_;
v___y_507_ = v___x_534_;
v_a_508_ = v___x_538_;
goto v___jp_505_;
}
else
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((size_t)0ULL);
v___x_540_ = lean_usize_of_nat(v___x_537_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_535_, v___x_539_, v___x_540_, v_a_449_, v_a_450_);
lean_dec(v___x_535_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; uint8_t v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = lean_unbox(v_a_542_);
lean_dec(v_a_542_);
v___y_506_ = v_a_531_;
v___y_507_ = v___x_534_;
v_a_508_ = v___x_543_;
goto v___jp_505_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_541_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v___y_491_ = v_a_531_;
v___y_492_ = v___x_534_;
v_a_493_ = v___x_549_;
goto v___jp_490_;
}
}
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_552_ = lean_io_get_num_heartbeats();
v___x_553_ = lean_st_ref_get(v___x_456_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v___x_553_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v___x_553_);
lean_dec(v_name_448_);
v___y_524_ = v___x_552_;
v___y_525_ = v_a_531_;
v_a_526_ = v___x_556_;
goto v___jp_523_;
}
else
{
if (v___x_556_ == 0)
{
lean_dec(v___x_553_);
lean_dec(v_name_448_);
v___y_524_ = v___x_552_;
v___y_525_ = v_a_531_;
v_a_526_ = v___x_556_;
goto v___jp_523_;
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_555_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_553_, v___x_557_, v___x_558_, v_a_449_, v_a_450_);
lean_dec(v___x_553_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_unbox(v_a_560_);
lean_dec(v_a_560_);
v___y_524_ = v___x_552_;
v___y_525_ = v_a_531_;
v_a_526_ = v___x_561_;
goto v___jp_523_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_a_562_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_559_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_512_ = v___x_552_;
v___y_513_ = v_a_531_;
v_a_514_ = v___x_567_;
goto v___jp_511_;
}
}
}
}
}
}
}
}
v___jp_458_:
{
if (lean_obj_tag(v___y_459_) == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_isSharedCheck_466_ = !lean_is_exclusive(v___y_459_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___y_459_, 0);
lean_dec(v_unused_467_);
v___x_461_ = v___y_459_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___y_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_457_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_457_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_a_468_ = lean_ctor_get(v___y_459_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_459_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___y_459_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___y_459_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_executeReservedNameAction(v_name_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_586_, lean_object* v_x_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_587_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_592_, lean_object* v_x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_592_, v_x_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_605_, lean_object* v_x_606_){
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
return v_suppressElabErrors_605_;
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
return v_suppressElabErrors_605_;
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
return v_suppressElabErrors_605_;
}
}
}
}
else
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
}
default: 
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
}
}
case 0:
{
lean_object* v_str_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_str_631_ = lean_ctor_get(v_x_606_, 1);
v___x_632_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_633_ = lean_string_dec_eq(v_str_631_, v___x_632_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
return v_suppressElabErrors_605_;
}
}
default: 
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
}
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_636_, lean_object* v_x_637_){
_start:
{
uint8_t v_suppressElabErrors_boxed_638_; uint8_t v_res_639_; lean_object* v_r_640_; 
v_suppressElabErrors_boxed_638_ = lean_unbox(v_suppressElabErrors_636_);
v_res_639_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_638_, v_x_637_);
lean_dec(v_x_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_641_, lean_object* v_msgData_642_, uint8_t v_severity_643_, uint8_t v_isSilent_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v_toCold_656_; lean_object* v___y_657_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; uint8_t v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; uint8_t v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_723_; uint8_t v___y_724_; uint8_t v___x_734_; uint8_t v___y_736_; uint8_t v___x_742_; 
v___x_734_ = 2;
v___x_742_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_734_);
if (v___x_742_ == 0)
{
v___y_736_ = v___x_742_;
goto v___jp_735_;
}
else
{
uint8_t v___x_743_; 
lean_inc_ref(v_msgData_642_);
v___x_743_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_642_);
if (v___x_743_ == 0)
{
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref(v_msgData_642_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
v___jp_648_:
{
lean_object* v_currNamespace_658_; lean_object* v_openDecls_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_env_664_; lean_object* v_nextMacroScope_665_; lean_object* v_ngen_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_cache_669_; lean_object* v_recordedDeps_670_; lean_object* v_messages_671_; lean_object* v_infoState_672_; lean_object* v_snapshotTasks_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v_currNamespace_658_ = lean_ctor_get(v_toCold_656_, 4);
v_openDecls_659_ = lean_ctor_get(v_toCold_656_, 5);
lean_inc(v_openDecls_659_);
lean_inc(v_currNamespace_658_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_currNamespace_658_);
lean_ctor_set(v___x_660_, 1, v_openDecls_659_);
v___x_661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___y_655_);
lean_inc_ref(v___y_652_);
lean_inc_ref(v___y_654_);
v___x_662_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_662_, 0, v___y_654_);
lean_ctor_set(v___x_662_, 1, v___y_651_);
lean_ctor_set(v___x_662_, 2, v___y_649_);
lean_ctor_set(v___x_662_, 3, v___y_652_);
lean_ctor_set(v___x_662_, 4, v___x_661_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*5, v___y_653_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*5 + 1, v___y_650_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*5 + 2, v_isSilent_644_);
v___x_663_ = lean_st_ref_take(v___y_657_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_665_ = lean_ctor_get(v___x_663_, 1);
v_ngen_666_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_663_, 3);
v_traceState_668_ = lean_ctor_get(v___x_663_, 4);
v_cache_669_ = lean_ctor_get(v___x_663_, 5);
v_recordedDeps_670_ = lean_ctor_get(v___x_663_, 6);
v_messages_671_ = lean_ctor_get(v___x_663_, 7);
v_infoState_672_ = lean_ctor_get(v___x_663_, 8);
v_snapshotTasks_673_ = lean_ctor_get(v___x_663_, 9);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_684_ == 0)
{
v___x_675_ = v___x_663_;
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snapshotTasks_673_);
lean_inc(v_infoState_672_);
lean_inc(v_messages_671_);
lean_inc(v_recordedDeps_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_668_);
lean_inc(v_auxDeclNGen_667_);
lean_inc(v_ngen_666_);
lean_inc(v_nextMacroScope_665_);
lean_inc(v_env_664_);
lean_dec(v___x_663_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_box(0);
v___x_678_ = l_Lean_MessageLog_add(v___x_662_, v_messages_671_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 7, v___x_678_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_env_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_nextMacroScope_665_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_ngen_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_auxDeclNGen_667_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_traceState_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v_recordedDeps_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_infoState_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 9, v_snapshotTasks_673_);
v___x_680_ = v_reuseFailAlloc_683_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_st_ref_put(v___y_657_, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_677_);
return v___x_682_;
}
}
}
v___jp_685_:
{
lean_object* v_fileName_694_; lean_object* v_fileMap_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_711_; 
v_fileName_694_ = lean_ctor_get(v___y_691_, 0);
v_fileMap_695_ = lean_ctor_get(v___y_691_, 1);
v___x_696_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_642_);
v___x_697_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_696_, v___y_645_, v___y_646_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_711_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_inc_ref_n(v_fileMap_695_, 2);
v___x_702_ = l_Lean_FileMap_toPosition(v_fileMap_695_, v___y_689_);
lean_dec(v___y_689_);
v___x_703_ = l_Lean_FileMap_toPosition(v_fileMap_695_, v___y_693_);
lean_dec(v___y_693_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_692_ == 0)
{
lean_del_object(v___x_700_);
lean_dec_ref(v___y_686_);
v___y_649_ = v___x_704_;
v___y_650_ = v___y_688_;
v___y_651_ = v___x_702_;
v___y_652_ = v___x_705_;
v___y_653_ = v___y_690_;
v___y_654_ = v_fileName_694_;
v___y_655_ = v_a_698_;
v_toCold_656_ = v___y_687_;
v___y_657_ = v___y_646_;
goto v___jp_648_;
}
else
{
uint8_t v___x_706_; 
lean_inc(v_a_698_);
v___x_706_ = l_Lean_MessageData_hasTag(v___y_686_, v_a_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec_ref_known(v___x_704_, 1);
lean_dec_ref(v___x_702_);
lean_dec(v_a_698_);
v___x_707_ = lean_box(0);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_707_);
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_del_object(v___x_700_);
v___y_649_ = v___x_704_;
v___y_650_ = v___y_688_;
v___y_651_ = v___x_702_;
v___y_652_ = v___x_705_;
v___y_653_ = v___y_690_;
v___y_654_ = v_fileName_694_;
v___y_655_ = v_a_698_;
v_toCold_656_ = v___y_687_;
v___y_657_ = v___y_646_;
goto v___jp_648_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Syntax_getTailPos_x3f(v___y_718_, v___y_717_);
lean_dec(v___y_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_inc(v___y_719_);
v___y_686_ = v___y_713_;
v___y_687_ = v___y_714_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_719_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_714_;
v___y_692_ = v___y_715_;
v___y_693_ = v___y_719_;
goto v___jp_685_;
}
else
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___y_686_ = v___y_713_;
v___y_687_ = v___y_714_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_719_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_714_;
v___y_692_ = v___y_715_;
v___y_693_ = v_val_721_;
goto v___jp_685_;
}
}
v___jp_722_:
{
lean_object* v_toCold_725_; lean_object* v_ref_726_; uint8_t v_suppressElabErrors_727_; lean_object* v___x_728_; lean_object* v___f_729_; lean_object* v_ref_730_; lean_object* v___x_731_; 
v_toCold_725_ = lean_ctor_get(v___y_645_, 0);
v_ref_726_ = lean_ctor_get(v___y_645_, 2);
v_suppressElabErrors_727_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 2);
v___x_728_ = lean_box(v_suppressElabErrors_727_);
v___f_729_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_729_, 0, v___x_728_);
v_ref_730_ = l_Lean_replaceRef(v_ref_641_, v_ref_726_);
v___x_731_ = l_Lean_Syntax_getPos_x3f(v_ref_730_, v___y_723_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_713_ = v___f_729_;
v___y_714_ = v_toCold_725_;
v___y_715_ = v_suppressElabErrors_727_;
v___y_716_ = v___y_724_;
v___y_717_ = v___y_723_;
v___y_718_ = v_ref_730_;
v___y_719_ = v___x_732_;
goto v___jp_712_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v___x_731_, 1);
v___y_713_ = v___f_729_;
v___y_714_ = v_toCold_725_;
v___y_715_ = v_suppressElabErrors_727_;
v___y_716_ = v___y_724_;
v___y_717_ = v___y_723_;
v___y_718_ = v_ref_730_;
v___y_719_ = v_val_733_;
goto v___jp_712_;
}
}
v___jp_735_:
{
uint8_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 1;
v___x_738_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_737_);
if (v___x_738_ == 0)
{
v___y_723_ = v___y_736_;
v___y_724_ = v_severity_643_;
goto v___jp_722_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_645_);
v___x_740_ = l_Lean_warningAsError;
v___x_741_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_739_, v___x_740_);
lean_dec_ref(v___x_739_);
if (v___x_741_ == 0)
{
v___y_723_ = v___y_736_;
v___y_724_ = v_severity_643_;
goto v___jp_722_;
}
else
{
v___y_723_ = v___y_736_;
v___y_724_ = v___x_734_;
goto v___jp_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_746_, lean_object* v_msgData_747_, lean_object* v_severity_748_, lean_object* v_isSilent_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v_severity_boxed_753_; uint8_t v_isSilent_boxed_754_; lean_object* v_res_755_; 
v_severity_boxed_753_ = lean_unbox(v_severity_748_);
v_isSilent_boxed_754_ = lean_unbox(v_isSilent_749_);
v_res_755_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_746_, v_msgData_747_, v_severity_boxed_753_, v_isSilent_boxed_754_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v_ref_746_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_756_, uint8_t v_severity_757_, uint8_t v_isSilent_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_ref_762_; lean_object* v___x_763_; 
v_ref_762_ = lean_ctor_get(v___y_759_, 2);
v___x_763_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_762_, v_msgData_756_, v_severity_757_, v_isSilent_758_, v___y_759_, v___y_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_764_, lean_object* v_severity_765_, lean_object* v_isSilent_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_severity_boxed_770_; uint8_t v_isSilent_boxed_771_; lean_object* v_res_772_; 
v_severity_boxed_770_ = lean_unbox(v_severity_765_);
v_isSilent_boxed_771_ = lean_unbox(v_isSilent_766_);
v_res_772_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_764_, v_severity_boxed_770_, v_isSilent_boxed_771_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = 2;
v___x_778_ = 0;
v___x_779_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_773_, v___x_777_, v___x_778_, v___y_774_, v___y_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_784_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v___x_797_; 
lean_dec(v_id_791_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_x_793_);
return v___x_797_;
}
else
{
lean_object* v_head_798_; lean_object* v_tail_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_857_; 
v_head_798_ = lean_ctor_get(v_x_792_, 0);
v_tail_799_ = lean_ctor_get(v_x_792_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_857_ == 0)
{
v___x_801_ = v_x_792_;
v_isShared_802_ = v_isSharedCheck_857_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_tail_799_);
lean_inc(v_head_798_);
lean_dec(v_x_792_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_857_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_fst_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v_env_811_; uint8_t v___x_812_; 
v_fst_808_ = lean_ctor_get(v_head_798_, 0);
v___x_809_ = 1;
v___x_810_ = lean_st_ref_get(v___y_795_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
lean_inc(v_fst_808_);
v___x_812_ = l_Lean_Environment_contains(v_env_811_, v_fst_808_, v___x_809_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_inc(v_fst_808_);
v___x_813_ = l_Lean_executeReservedNameAction(v_fst_808_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_814_; lean_object* v_env_815_; uint8_t v___x_816_; 
lean_dec_ref_known(v___x_813_, 1);
v___x_814_ = lean_st_ref_get(v___y_795_);
v_env_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc_ref(v_env_815_);
lean_dec(v___x_814_);
v___x_816_ = l_Lean_Environment_containsOnBranch(v_env_815_, v_fst_808_);
lean_dec_ref(v_env_815_);
if (v___x_816_ == 0)
{
lean_del_object(v___x_801_);
lean_dec(v_head_798_);
v_x_792_ = v_tail_799_;
goto _start;
}
else
{
goto v___jp_803_;
}
}
else
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_854_; 
lean_del_object(v___x_801_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_head_798_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_head_798_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_head_798_, 0);
lean_dec(v_unused_856_);
v___x_819_ = v_head_798_;
v_isShared_820_ = v_isSharedCheck_854_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_head_798_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_854_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_853_; 
v_a_821_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_853_ == 0)
{
v___x_823_ = v___x_813_;
v_isShared_824_ = v_isSharedCheck_853_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_813_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_853_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_Exception_isInterrupt(v_a_821_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
lean_inc(v_a_821_);
v___x_826_ = l_Lean_Exception_isRuntime(v_a_821_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_del_object(v___x_823_);
v___x_827_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_791_);
v___x_828_ = l_Lean_MessageData_ofName(v_id_791_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 7);
lean_ctor_set(v___x_819_, 1, v___x_828_);
lean_ctor_set(v___x_819_, 0, v___x_827_);
v___x_830_ = v___x_819_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_846_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_831_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Exception_toMessageData(v_a_821_);
v___x_834_ = l_Lean_indentD(v___x_833_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_832_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_835_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_dec_ref_known(v___x_836_, 1);
v_x_792_ = v_tail_799_;
goto _start;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_tail_799_);
lean_dec(v_x_793_);
lean_dec(v_id_791_);
v_a_838_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
else
{
lean_object* v___x_848_; 
lean_del_object(v___x_819_);
lean_dec(v_tail_799_);
lean_dec(v_x_793_);
lean_dec(v_id_791_);
if (v_isShared_824_ == 0)
{
v___x_848_ = v___x_823_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_821_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v___x_851_; 
lean_del_object(v___x_819_);
lean_dec(v_tail_799_);
lean_dec(v_x_793_);
lean_dec(v_id_791_);
if (v_isShared_824_ == 0)
{
v___x_851_ = v___x_823_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_821_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
else
{
goto v___jp_803_;
}
v___jp_803_:
{
lean_object* v___x_805_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_x_793_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_head_798_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_x_793_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v_x_792_ = v_tail_799_;
v_x_793_ = v___x_805_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_858_, v_x_859_, v_x_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_866_; 
v___x_866_ = lean_box(0);
return v___x_866_;
}
else
{
lean_object* v_head_867_; lean_object* v_tail_868_; lean_object* v_fst_869_; uint8_t v___x_870_; 
v_head_867_ = lean_ctor_get(v_x_865_, 0);
v_tail_868_ = lean_ctor_get(v_x_865_, 1);
v_fst_869_ = lean_ctor_get(v_head_867_, 0);
v___x_870_ = l_Lean_isPrivateName(v_fst_869_);
if (v___x_870_ == 0)
{
v_x_865_ = v_tail_868_;
goto _start;
}
else
{
lean_object* v___x_872_; 
lean_inc(v_head_867_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_head_867_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_873_);
lean_dec(v_x_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; 
v___x_879_ = 1;
v___x_880_ = 0;
v___x_881_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_875_, v___x_879_, v___x_880_, v___y_876_, v___y_877_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_888_);
v___x_891_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v___x_890_, v_opt_887_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_box(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_894_, v___y_895_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_opt_894_);
return v_res_897_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_env_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_931_; 
v___x_908_ = lean_st_ref_get(v___y_906_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_908_);
v___x_910_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_911_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_910_, v___y_905_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_931_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_931_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_931_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
uint8_t v_isExporting_921_; 
v_isExporting_921_ = lean_ctor_get_uint8(v_env_909_, sizeof(void*)*13);
lean_dec_ref(v_env_909_);
if (v_isExporting_921_ == 0)
{
lean_dec(v_a_912_);
lean_dec(v_id_904_);
goto v___jp_916_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_isPrivateName(v_id_904_);
if (v___x_922_ == 0)
{
lean_dec(v_a_912_);
lean_dec(v_id_904_);
goto v___jp_916_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_923_ == 0)
{
lean_dec(v_id_904_);
goto v___jp_916_;
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_del_object(v___x_914_);
v___x_924_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_925_ = 0;
v___x_926_ = l_Lean_MessageData_ofConstName(v_id_904_, v___x_925_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_924_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_929_, v___y_905_, v___y_906_);
return v___x_930_;
}
}
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_937_, uint8_t v_enableLog_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_toCold_943_; lean_object* v_env_944_; lean_object* v_currNamespace_945_; lean_object* v_openDecls_946_; lean_object* v___x_947_; lean_object* v_res_948_; lean_object* v___x_949_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_toCold_943_ = lean_ctor_get(v___y_939_, 0);
v_env_944_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_env_944_);
lean_dec(v___x_942_);
v_currNamespace_945_ = lean_ctor_get(v_toCold_943_, 4);
v_openDecls_946_ = lean_ctor_get(v_toCold_943_, 5);
v___x_947_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_939_);
lean_inc(v_openDecls_946_);
lean_inc(v_currNamespace_945_);
v_res_948_ = l_Lean_ResolveName_resolveGlobalName(v_env_944_, v___x_947_, v_currNamespace_945_, v_openDecls_946_, v_id_937_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_st_ref_get(v___y_940_);
if (v_enableLog_938_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v___x_949_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_res_948_);
return v___x_950_;
}
else
{
lean_object* v_env_951_; uint8_t v_isExporting_952_; 
v_env_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_949_);
v_isExporting_952_ = lean_ctor_get_uint8(v_env_951_, sizeof(void*)*13);
lean_dec_ref(v_env_951_);
if (v_isExporting_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_res_948_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_948_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_val_955_; lean_object* v_fst_956_; lean_object* v___x_957_; 
v_val_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_954_, 1);
v_fst_956_ = lean_ctor_get(v_val_955_, 0);
lean_inc(v_fst_956_);
lean_dec(v_val_955_);
v___x_957_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_956_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_965_);
v___x_959_ = v___x_957_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_957_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_res_948_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_res_948_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_res_948_);
v_a_966_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_957_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_957_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_974_; 
lean_dec(v___x_954_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_res_948_);
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_975_, lean_object* v_enableLog_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v_enableLog_boxed_980_; lean_object* v_res_981_; 
v_enableLog_boxed_980_ = lean_unbox(v_enableLog_976_);
v_res_981_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_975_, v_enableLog_boxed_980_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
uint8_t v___x_986_; lean_object* v___x_987_; 
v___x_986_ = 1;
lean_inc(v_id_982_);
v___x_987_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_982_, v___x_986_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_box(0);
v___x_990_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_982_, v_a_988_, v___x_989_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_List_reverse___redArg(v_a_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
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
else
{
return v___x_990_;
}
}
else
{
lean_dec(v_id_982_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_realizeGlobalName(v_id_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1005_, v___y_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec_ref(v_opt_1010_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
if (lean_obj_tag(v_a_1015_) == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = l_List_reverse___redArg(v_a_1016_);
return v___x_1017_;
}
else
{
lean_object* v_head_1018_; lean_object* v_tail_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
v_head_1018_ = lean_ctor_get(v_a_1015_, 0);
v_tail_1019_ = lean_ctor_get(v_a_1015_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_1015_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1021_ = v_a_1015_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_tail_1019_);
lean_inc(v_head_1018_);
lean_dec(v_a_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_fst_1023_; lean_object* v___x_1025_; 
v_fst_1023_ = lean_ctor_get(v_head_1018_, 0);
lean_inc(v_fst_1023_);
lean_dec(v_head_1018_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_a_1016_);
lean_ctor_set(v___x_1021_, 0, v_fst_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_fst_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_a_1016_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
v_a_1015_ = v_tail_1019_;
v_a_1016_ = v___x_1025_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_ref_1033_; lean_object* v___x_1034_; lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_ref_1033_ = lean_ctor_get(v___y_1030_, 2);
v___x_1034_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1029_, v___y_1030_, v___y_1031_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc(v_ref_1033_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_ref_1033_);
lean_ctor_set(v___x_1039_, 1, v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1049_, lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_toCold_1054_; lean_object* v_currRecDepth_1055_; lean_object* v_ref_1056_; uint16_t v_optionFlags_1057_; uint8_t v_suppressElabErrors_1058_; uint8_t v_checkDeprecated_1059_; uint8_t v_isRecordingDeps_1060_; lean_object* v_ref_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_toCold_1054_ = lean_ctor_get(v___y_1051_, 0);
v_currRecDepth_1055_ = lean_ctor_get(v___y_1051_, 1);
v_ref_1056_ = lean_ctor_get(v___y_1051_, 2);
v_optionFlags_1057_ = lean_ctor_get_uint16(v___y_1051_, sizeof(void*)*3);
v_suppressElabErrors_1058_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*3 + 2);
v_checkDeprecated_1059_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1060_ = lean_ctor_get_uint8(v___y_1051_, sizeof(void*)*3 + 4);
v_ref_1061_ = l_Lean_replaceRef(v_ref_1049_, v_ref_1056_);
lean_inc(v_currRecDepth_1055_);
lean_inc_ref(v_toCold_1054_);
v___x_1062_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1062_, 0, v_toCold_1054_);
lean_ctor_set(v___x_1062_, 1, v_currRecDepth_1055_);
lean_ctor_set(v___x_1062_, 2, v_ref_1061_);
lean_ctor_set_uint16(v___x_1062_, sizeof(void*)*3, v_optionFlags_1057_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3 + 2, v_suppressElabErrors_1058_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3 + 3, v_checkDeprecated_1059_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3 + 4, v_isRecordingDeps_1060_);
v___x_1063_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1050_, v___x_1062_, v___y_1052_);
lean_dec_ref_known(v___x_1062_, 3);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1064_, v_msg_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v_ref_1064_);
return v_res_1069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1091_, lean_object* v_declHint_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_env_1097_; uint8_t v___x_1098_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_st_ref_get(v___y_1093_);
v_env_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_env_1097_);
lean_dec(v___x_1096_);
v___x_1098_ = l_Lean_Name_isAnonymous(v_declHint_1092_);
if (v___x_1098_ == 0)
{
uint8_t v_isExporting_1099_; 
v_isExporting_1099_ = lean_ctor_get_uint8(v_env_1097_, sizeof(void*)*13);
if (v_isExporting_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v_env_1097_);
lean_dec(v_declHint_1092_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_msg_1091_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
lean_inc_ref(v_env_1097_);
v___x_1101_ = l_Lean_Environment_setExporting(v_env_1097_, v___x_1098_);
lean_inc(v_declHint_1092_);
lean_inc_ref(v___x_1101_);
v___x_1102_ = l_Lean_Environment_contains(v___x_1101_, v_declHint_1092_, v_isExporting_1099_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_env_1097_);
lean_dec(v_declHint_1092_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_msg_1091_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_c_1109_; lean_object* v___x_1110_; 
v___x_1104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1105_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1106_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1101_);
v___x_1107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1101_);
lean_ctor_set(v___x_1107_, 1, v___x_1104_);
lean_ctor_set(v___x_1107_, 2, v___x_1105_);
lean_ctor_set(v___x_1107_, 3, v___x_1106_);
lean_inc(v_declHint_1092_);
v___x_1108_ = l_Lean_MessageData_ofConstName(v_declHint_1092_, v___x_1098_);
v_c_1109_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1109_, 0, v___x_1107_);
lean_ctor_set(v_c_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1101_, v_declHint_1092_);
lean_dec_ref(v___x_1101_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_env_1097_);
lean_dec(v_declHint_1092_);
v___x_1111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_c_1109_);
v___x_1113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_MessageData_note(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_msg_1091_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1152_; 
v_val_1118_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1120_ = v___x_1110_;
v_isShared_1121_ = v_isSharedCheck_1152_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v___x_1110_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1152_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v_moduleNames_1123_; lean_object* v_mod_1124_; uint8_t v___x_1125_; 
v___x_1122_ = l_Lean_Environment_header(v_env_1097_);
lean_dec_ref(v_env_1097_);
v_moduleNames_1123_ = lean_ctor_get(v___x_1122_, 4);
lean_inc_ref(v_moduleNames_1123_);
lean_dec_ref(v___x_1122_);
v_mod_1124_ = lean_array_get(v___x_1095_, v_moduleNames_1123_, v_val_1118_);
lean_dec(v_val_1118_);
lean_dec_ref(v_moduleNames_1123_);
v___x_1125_ = l_Lean_isPrivateName(v_declHint_1092_);
lean_dec(v_declHint_1092_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_c_1109_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_ofName(v_mod_1124_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_note(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1091_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1135_);
v___x_1137_ = v___x_1120_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v_c_1109_);
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_ofName(v_mod_1124_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_MessageData_note(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1091_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1148_);
v___x_1150_ = v___x_1120_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec_ref(v_env_1097_);
lean_dec(v_declHint_1092_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1091_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1154_, lean_object* v_declHint_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1154_, v_declHint_1155_, v___y_1156_);
lean_dec(v___y_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v___x_1164_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1159_, v_declHint_1160_, v___y_1162_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = l_Lean_unknownIdentifierMessageTag;
v___x_1170_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1181_, lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1189_; 
v___x_1187_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1181_, v_a_1188_, v___y_1184_, v___y_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v_declHint_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1190_, v_msg_1191_, v_declHint_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_ref_1190_);
return v_res_1196_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1203_, lean_object* v_constName_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1208_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1209_ = 0;
lean_inc(v_constName_1204_);
v___x_1210_ = l_Lean_MessageData_ofConstName(v_constName_1204_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1208_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1203_, v___x_1213_, v_constName_1204_, v___y_1205_, v___y_1206_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1215_, lean_object* v_constName_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1215_, v_constName_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_ref_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
if (lean_obj_tag(v_a_1221_) == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = l_List_reverse___redArg(v_a_1222_);
return v___x_1223_;
}
else
{
lean_object* v_head_1224_; lean_object* v_tail_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_head_1224_ = lean_ctor_get(v_a_1221_, 0);
v_tail_1225_ = lean_ctor_get(v_a_1221_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1221_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v_a_1221_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_tail_1225_);
lean_inc(v_head_1224_);
lean_dec(v_a_1221_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_snd_1229_; uint8_t v___x_1230_; 
v_snd_1229_ = lean_ctor_get(v_head_1224_, 1);
v___x_1230_ = l_List_isEmpty___redArg(v_snd_1229_);
if (v___x_1230_ == 0)
{
lean_del_object(v___x_1227_);
lean_dec(v_head_1224_);
v_a_1221_ = v_tail_1225_;
goto _start;
}
else
{
lean_object* v___x_1233_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_a_1222_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_head_1224_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_a_1222_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v_a_1221_ = v_tail_1225_;
v_a_1222_ = v___x_1233_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1237_, lean_object* v_cs_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_cs_1243_; uint8_t v___x_1247_; 
v___x_1242_ = lean_box(0);
v_cs_1243_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1238_, v___x_1242_);
v___x_1247_ = l_List_isEmpty___redArg(v_cs_1243_);
if (v___x_1247_ == 0)
{
lean_dec(v_n_1237_);
goto v___jp_1244_;
}
else
{
lean_object* v_ref_1248_; lean_object* v___x_1249_; lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_cs_1243_);
v_ref_1248_ = lean_ctor_get(v___y_1239_, 2);
v___x_1249_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1248_, v_n_1237_, v___y_1239_, v___y_1240_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
v___jp_1244_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1243_, v___x_1242_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1258_, lean_object* v_cs_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1258_, v_cs_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
lean_inc(v_n_1264_);
v___x_1268_ = l_Lean_realizeGlobalName(v_n_1264_, v_a_1265_, v_a_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1264_, v_a_1269_, v_a_1265_, v_a_1266_);
return v___x_1270_;
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_n_1264_);
v_a_1271_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1268_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1268_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_realizeGlobalConstCore(v_n_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1285_, v_constName_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_ref_1292_, lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1291_, v_ref_1292_, v_constName_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_ref_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1298_, lean_object* v_ref_1299_, lean_object* v_msg_1300_, lean_object* v_declHint_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1299_, v_msg_1300_, v_declHint_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1306_, v_ref_1307_, v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_ref_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1314_, lean_object* v_declHint_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1314_, v_declHint_1315_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1320_, lean_object* v_declHint_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1320_, v_declHint_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1326_, lean_object* v_ref_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1327_, v_msg_1328_, v___y_1329_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_ref_1334_, lean_object* v_msg_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1333_, v_ref_1334_, v_msg_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v_ref_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1340_, lean_object* v_msg_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1341_, v___y_1342_, v___y_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_msg_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1346_, v_msg_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
if (lean_obj_tag(v_a_1352_) == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = l_List_reverse___redArg(v_a_1353_);
return v___x_1354_;
}
else
{
lean_object* v_head_1355_; lean_object* v_tail_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1365_; 
v_head_1355_ = lean_ctor_get(v_a_1352_, 0);
v_tail_1356_ = lean_ctor_get(v_a_1352_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_a_1352_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1358_ = v_a_1352_;
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_tail_1356_);
lean_inc(v_head_1355_);
lean_dec(v_a_1352_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_MessageData_ofExpr(v_head_1355_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_a_1353_);
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1353_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v_a_1352_ = v_tail_1356_;
v_a_1353_ = v___x_1362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
if (lean_obj_tag(v_a_1366_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_List_reverse___redArg(v_a_1367_);
return v___x_1368_;
}
else
{
lean_object* v_head_1369_; lean_object* v_tail_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1380_; 
v_head_1369_ = lean_ctor_get(v_a_1366_, 0);
v_tail_1370_ = lean_ctor_get(v_a_1366_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1366_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1372_ = v_a_1366_;
v_isShared_1373_ = v_isSharedCheck_1380_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_tail_1370_);
lean_inc(v_head_1369_);
lean_dec(v_a_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1380_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Lean_mkConst(v_head_1369_, v___x_1374_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_a_1367_);
lean_ctor_set(v___x_1372_, 0, v___x_1375_);
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1367_);
v___x_1377_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v_a_1366_ = v_tail_1370_;
v_a_1367_ = v___x_1377_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1387_, lean_object* v_cs_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
if (lean_obj_tag(v_cs_1388_) == 1)
{
lean_object* v_tail_1404_; 
v_tail_1404_ = lean_ctor_get(v_cs_1388_, 1);
if (lean_obj_tag(v_tail_1404_) == 0)
{
lean_object* v_head_1405_; lean_object* v___x_1406_; 
lean_dec(v_n_1387_);
v_head_1405_ = lean_ctor_get(v_cs_1388_, 0);
lean_inc(v_head_1405_);
lean_dec_ref_known(v_cs_1388_, 2);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_head_1405_);
return v___x_1406_;
}
else
{
goto v___jp_1392_;
}
}
else
{
goto v___jp_1392_;
}
v___jp_1392_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1393_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1394_ = l_Lean_MessageData_ofName(v_n_1387_);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = lean_box(0);
v___x_1399_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1388_, v___x_1398_);
v___x_1400_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1399_, v___x_1398_);
v___x_1401_ = l_Lean_MessageData_ofList(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1397_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1402_, v___y_1389_, v___y_1390_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1407_, lean_object* v_cs_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1407_, v_cs_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; 
lean_inc(v_n_1413_);
v___x_1417_ = l_Lean_realizeGlobalConstCore(v_n_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1413_, v_a_1418_, v_a_1414_, v_a_1415_);
return v___x_1419_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_n_1413_);
v_a_1420_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1417_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1417_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_array_to_list(v_a_1434_);
return v___x_1435_;
}
else
{
lean_object* v_head_1436_; 
v_head_1436_ = lean_ctor_get(v_a_1433_, 0);
if (lean_obj_tag(v_head_1436_) == 1)
{
lean_object* v_fields_1437_; 
v_fields_1437_ = lean_ctor_get(v_head_1436_, 1);
if (lean_obj_tag(v_fields_1437_) == 0)
{
lean_object* v_tail_1438_; lean_object* v_n_1439_; lean_object* v___x_1440_; 
lean_inc_ref(v_head_1436_);
v_tail_1438_ = lean_ctor_get(v_a_1433_, 1);
lean_inc(v_tail_1438_);
lean_dec_ref_known(v_a_1433_, 2);
v_n_1439_ = lean_ctor_get(v_head_1436_, 0);
lean_inc(v_n_1439_);
lean_dec_ref_known(v_head_1436_, 2);
v___x_1440_ = lean_array_push(v_a_1434_, v_n_1439_);
v_a_1433_ = v_tail_1438_;
v_a_1434_ = v___x_1440_;
goto _start;
}
else
{
lean_object* v_tail_1442_; 
v_tail_1442_ = lean_ctor_get(v_a_1433_, 1);
lean_inc(v_tail_1442_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_tail_1442_;
goto _start;
}
}
else
{
lean_object* v_tail_1444_; 
v_tail_1444_ = lean_ctor_get(v_a_1433_, 1);
lean_inc(v_tail_1444_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_tail_1444_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1452_ = l_Lean_MessageData_ofFormat(v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1453_, lean_object* v_k_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
if (lean_obj_tag(v_stx_1453_) == 3)
{
lean_object* v_val_1458_; lean_object* v_preresolved_1459_; lean_object* v___x_1460_; lean_object* v_pre_1461_; uint8_t v___x_1462_; 
v_val_1458_ = lean_ctor_get(v_stx_1453_, 2);
lean_inc(v_val_1458_);
v_preresolved_1459_ = lean_ctor_get(v_stx_1453_, 3);
v___x_1460_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1459_);
v_pre_1461_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1459_, v___x_1460_);
v___x_1462_ = l_List_isEmpty___redArg(v_pre_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_val_1458_);
lean_dec_ref_known(v_stx_1453_, 4);
lean_dec_ref(v_k_1454_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_pre_1461_);
return v___x_1463_;
}
else
{
lean_object* v_toCold_1464_; lean_object* v_currRecDepth_1465_; lean_object* v_ref_1466_; uint16_t v_optionFlags_1467_; uint8_t v_suppressElabErrors_1468_; uint8_t v_checkDeprecated_1469_; uint8_t v_isRecordingDeps_1470_; lean_object* v_ref_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_pre_1461_);
v_toCold_1464_ = lean_ctor_get(v___y_1455_, 0);
v_currRecDepth_1465_ = lean_ctor_get(v___y_1455_, 1);
v_ref_1466_ = lean_ctor_get(v___y_1455_, 2);
v_optionFlags_1467_ = lean_ctor_get_uint16(v___y_1455_, sizeof(void*)*3);
v_suppressElabErrors_1468_ = lean_ctor_get_uint8(v___y_1455_, sizeof(void*)*3 + 2);
v_checkDeprecated_1469_ = lean_ctor_get_uint8(v___y_1455_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1470_ = lean_ctor_get_uint8(v___y_1455_, sizeof(void*)*3 + 4);
v_ref_1471_ = l_Lean_replaceRef(v_stx_1453_, v_ref_1466_);
lean_dec_ref_known(v_stx_1453_, 4);
lean_inc(v_currRecDepth_1465_);
lean_inc_ref(v_toCold_1464_);
v___x_1472_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1472_, 0, v_toCold_1464_);
lean_ctor_set(v___x_1472_, 1, v_currRecDepth_1465_);
lean_ctor_set(v___x_1472_, 2, v_ref_1471_);
lean_ctor_set_uint16(v___x_1472_, sizeof(void*)*3, v_optionFlags_1467_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3 + 2, v_suppressElabErrors_1468_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3 + 3, v_checkDeprecated_1469_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3 + 4, v_isRecordingDeps_1470_);
lean_inc(v___y_1456_);
v___x_1473_ = lean_apply_4(v_k_1454_, v_val_1458_, v___x_1472_, v___y_1456_, lean_box(0));
return v___x_1473_;
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec_ref(v_k_1454_);
v___x_1474_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1453_, v___x_1474_, v___y_1455_, v___y_1456_);
lean_dec(v_stx_1453_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1476_, lean_object* v_k_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1476_, v_k_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_toCold_1487_; lean_object* v_currRecDepth_1488_; lean_object* v_ref_1489_; uint16_t v_optionFlags_1490_; uint8_t v_suppressElabErrors_1491_; uint8_t v_checkDeprecated_1492_; uint8_t v_isRecordingDeps_1493_; lean_object* v___x_1494_; lean_object* v_ref_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_toCold_1487_ = lean_ctor_get(v_a_1484_, 0);
v_currRecDepth_1488_ = lean_ctor_get(v_a_1484_, 1);
v_ref_1489_ = lean_ctor_get(v_a_1484_, 2);
v_optionFlags_1490_ = lean_ctor_get_uint16(v_a_1484_, sizeof(void*)*3);
v_suppressElabErrors_1491_ = lean_ctor_get_uint8(v_a_1484_, sizeof(void*)*3 + 2);
v_checkDeprecated_1492_ = lean_ctor_get_uint8(v_a_1484_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1493_ = lean_ctor_get_uint8(v_a_1484_, sizeof(void*)*3 + 4);
v___x_1494_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1495_ = l_Lean_replaceRef(v_stx_1483_, v_ref_1489_);
lean_inc(v_currRecDepth_1488_);
lean_inc_ref(v_toCold_1487_);
v___x_1496_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1496_, 0, v_toCold_1487_);
lean_ctor_set(v___x_1496_, 1, v_currRecDepth_1488_);
lean_ctor_set(v___x_1496_, 2, v_ref_1495_);
lean_ctor_set_uint16(v___x_1496_, sizeof(void*)*3, v_optionFlags_1490_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*3 + 2, v_suppressElabErrors_1491_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*3 + 3, v_checkDeprecated_1492_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*3 + 4, v_isRecordingDeps_1493_);
v___x_1497_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1483_, v___x_1494_, v___x_1496_, v_a_1485_);
lean_dec_ref_known(v___x_1496_, 3);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_realizeGlobalConst(v_stx_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1502_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_instMonadEIO___redArg();
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_toApplicative_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1543_; 
v___x_1510_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1511_ = l_StateRefT_x27_instMonad___redArg(v___x_1510_);
v_toApplicative_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1511_, 1);
lean_dec(v_unused_1544_);
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_toApplicative_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_toFunctor_1516_; lean_object* v_toSeq_1517_; lean_object* v_toSeqLeft_1518_; lean_object* v_toSeqRight_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1541_; 
v_toFunctor_1516_ = lean_ctor_get(v_toApplicative_1512_, 0);
v_toSeq_1517_ = lean_ctor_get(v_toApplicative_1512_, 2);
v_toSeqLeft_1518_ = lean_ctor_get(v_toApplicative_1512_, 3);
v_toSeqRight_1519_ = lean_ctor_get(v_toApplicative_1512_, 4);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_toApplicative_1512_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v_toApplicative_1512_, 1);
lean_dec(v_unused_1542_);
v___x_1521_ = v_toApplicative_1512_;
v_isShared_1522_ = v_isSharedCheck_1541_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_toSeqRight_1519_);
lean_inc(v_toSeqLeft_1518_);
lean_inc(v_toSeq_1517_);
lean_inc(v_toFunctor_1516_);
lean_dec(v_toApplicative_1512_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1541_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___x_1532_; 
v___f_1523_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1524_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1516_);
v___f_1525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1525_, 0, v_toFunctor_1516_);
v___f_1526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1526_, 0, v_toFunctor_1516_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___f_1525_);
lean_ctor_set(v___x_1527_, 1, v___f_1526_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toSeqRight_1519_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toSeqLeft_1518_);
v___f_1530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1530_, 0, v_toSeq_1517_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___f_1528_);
lean_ctor_set(v___x_1521_, 3, v___f_1529_);
lean_ctor_set(v___x_1521_, 2, v___f_1530_);
lean_ctor_set(v___x_1521_, 1, v___f_1523_);
lean_ctor_set(v___x_1521_, 0, v___x_1527_);
v___x_1532_ = v___x_1521_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___f_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v___f_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v___f_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v___f_1528_);
v___x_1532_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___f_1524_);
lean_ctor_set(v___x_1514_, 0, v___x_1532_);
v___x_1534_ = v___x_1514_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___f_1524_);
v___x_1534_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_195__overap_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = l_instInhabitedOfMonad___redArg(v___x_1534_, v___x_1535_);
v___x_195__overap_1537_ = lean_panic_fn_borrowed(v___x_1536_, v_msg_1506_);
lean_dec(v___x_1536_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
v___x_1538_ = lean_apply_3(v___x_195__overap_1537_, v___y_1507_, v___y_1508_, lean_box(0));
return v___x_1538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
return v_x_1551_;
}
else
{
lean_object* v_head_1553_; lean_object* v_tail_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_head_1553_ = lean_ctor_get(v_x_1552_, 0);
v_tail_1554_ = lean_ctor_get(v_x_1552_, 1);
v___x_1555_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1556_ = lean_string_append(v_x_1551_, v___x_1555_);
v___x_1557_ = lean_expr_dbg_to_string(v_head_1553_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v_x_1551_ = v___x_1558_;
v_x_1552_ = v_tail_1554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1560_, v_x_1561_);
lean_dec(v_x_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1567_;
}
else
{
lean_object* v_tail_1568_; 
v_tail_1568_ = lean_ctor_get(v_x_1566_, 1);
if (lean_obj_tag(v_tail_1568_) == 0)
{
lean_object* v_head_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_head_1569_ = lean_ctor_get(v_x_1566_, 0);
v___x_1570_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1571_ = lean_expr_dbg_to_string(v_head_1569_);
v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1574_ = lean_string_append(v___x_1572_, v___x_1573_);
return v___x_1574_;
}
else
{
lean_object* v_head_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint32_t v___x_1580_; lean_object* v___x_1581_; 
v_head_1575_ = lean_ctor_get(v_x_1566_, 0);
v___x_1576_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1577_ = lean_expr_dbg_to_string(v_head_1575_);
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1578_, v_tail_1568_);
v___x_1580_ = 93;
v___x_1581_ = lean_string_push(v___x_1579_, v___x_1580_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1582_);
lean_dec(v_x_1582_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1588_ = lean_unsigned_to_nat(11u);
v___x_1589_ = lean_unsigned_to_nat(429u);
v___x_1590_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1591_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1592_ = l_mkPanicMessageWithDecl(v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_, v___x_1587_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1595_, lean_object* v_cs_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
if (lean_obj_tag(v_cs_1596_) == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_id_1595_);
v___x_1600_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1601_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1600_, v___y_1597_, v___y_1598_);
return v___x_1601_;
}
else
{
lean_object* v_tail_1602_; 
v_tail_1602_ = lean_ctor_get(v_cs_1596_, 1);
if (lean_obj_tag(v_tail_1602_) == 0)
{
lean_object* v_head_1603_; lean_object* v___x_1604_; 
lean_dec(v_id_1595_);
v_head_1603_ = lean_ctor_get(v_cs_1596_, 0);
lean_inc(v_head_1603_);
lean_dec_ref_known(v_cs_1596_, 2);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_head_1603_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1605_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1606_ = lean_box(0);
v___x_1607_ = 0;
lean_inc(v_id_1595_);
v___x_1608_ = l_Lean_Syntax_formatStx(v_id_1595_, v___x_1606_, v___x_1607_);
v___x_1609_ = l_Std_Format_defWidth;
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = l_Std_Format_pretty(v___x_1608_, v___x_1609_, v___x_1610_, v___x_1610_);
v___x_1612_ = lean_string_append(v___x_1605_, v___x_1611_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
v___x_1615_ = lean_box(0);
v___x_1616_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1596_, v___x_1615_);
v___x_1617_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1616_);
lean_dec(v___x_1616_);
v___x_1618_ = lean_string_append(v___x_1614_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = l_Lean_MessageData_ofFormat(v___x_1619_);
v___x_1621_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1595_, v___x_1620_, v___y_1597_, v___y_1598_);
lean_dec(v_id_1595_);
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1622_, lean_object* v_cs_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1622_, v_cs_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; 
lean_inc(v_id_1628_);
v___x_1632_ = l_Lean_realizeGlobalConst(v_id_1628_, v_a_1629_, v_a_1630_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1628_, v_a_1633_, v_a_1629_, v_a_1630_);
return v___x_1634_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_id_1628_);
v_a_1635_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1632_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1632_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_realizeGlobalConstNoOverload(v_id_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1647_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(3863082579u);
v___x_1680_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1681_ = l_Lean_Name_num___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1684_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1685_ = l_Lean_Name_str___override(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1688_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1689_ = l_Lean_Name_str___override(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_unsigned_to_nat(2u);
v___x_1691_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1692_ = l_Lean_Name_num___override(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1695_ = 0;
v___x_1696_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1697_ = l_Lean_registerTraceClass(v___x_1694_, v___x_1695_, v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1699_;
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

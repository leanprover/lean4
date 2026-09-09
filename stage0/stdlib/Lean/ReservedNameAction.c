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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
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
lean_object* v___x_36_; lean_object* v_traceState_37_; lean_object* v_traces_38_; lean_object* v___x_39_; lean_object* v_traceState_40_; lean_object* v_env_41_; lean_object* v_nextMacroScope_42_; lean_object* v_ngen_43_; lean_object* v_auxDeclNGen_44_; lean_object* v_cache_45_; lean_object* v_messages_46_; lean_object* v_infoState_47_; lean_object* v_snapshotTasks_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_67_; 
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
v_messages_46_ = lean_ctor_get(v___x_39_, 6);
v_infoState_47_ = lean_ctor_get(v___x_39_, 7);
v_snapshotTasks_48_ = lean_ctor_get(v___x_39_, 8);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_67_ == 0)
{
v___x_50_ = v___x_39_;
v_isShared_51_ = v_isSharedCheck_67_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_snapshotTasks_48_);
lean_inc(v_infoState_47_);
lean_inc(v_messages_46_);
lean_inc(v_cache_45_);
lean_inc(v_traceState_40_);
lean_inc(v_auxDeclNGen_44_);
lean_inc(v_ngen_43_);
lean_inc(v_nextMacroScope_42_);
lean_inc(v_env_41_);
lean_dec(v___x_39_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_67_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
uint64_t v_tid_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_65_; 
v_tid_52_ = lean_ctor_get_uint64(v_traceState_40_, sizeof(void*)*1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_traceState_40_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v_traceState_40_, 0);
lean_dec(v_unused_66_);
v___x_54_ = v_traceState_40_;
v_isShared_55_ = v_isSharedCheck_65_;
goto v_resetjp_53_;
}
else
{
lean_dec(v_traceState_40_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_65_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_56_);
lean_ctor_set_uint64(v_reuseFailAlloc_64_, sizeof(void*)*1, v_tid_52_);
v___x_58_ = v_reuseFailAlloc_64_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 4, v___x_58_);
v___x_60_ = v___x_50_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_env_41_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_nextMacroScope_42_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_ngen_43_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_auxDeclNGen_44_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_63_, 5, v_cache_45_);
lean_ctor_set(v_reuseFailAlloc_63_, 6, v_messages_46_);
lean_ctor_set(v_reuseFailAlloc_63_, 7, v_infoState_47_);
lean_ctor_set(v_reuseFailAlloc_63_, 8, v_snapshotTasks_48_);
v___x_60_ = v_reuseFailAlloc_63_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_st_ref_put(v___y_34_, v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_traces_38_);
return v___x_62_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_68_);
lean_dec(v___y_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(lean_object* v_opts_79_, lean_object* v_opt_80_){
_start:
{
lean_object* v_name_81_; lean_object* v_defValue_82_; lean_object* v_map_83_; lean_object* v___x_84_; 
v_name_81_ = lean_ctor_get(v_opt_80_, 0);
v_defValue_82_ = lean_ctor_get(v_opt_80_, 1);
v_map_83_ = lean_ctor_get(v_opts_79_, 0);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_83_, v_name_81_);
if (lean_obj_tag(v___x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_unbox(v_defValue_82_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_84_, 1);
if (lean_obj_tag(v_val_86_) == 1)
{
uint8_t v_v_87_; 
v_v_87_ = lean_ctor_get_uint8(v_val_86_, 0);
lean_dec_ref_known(v_val_86_, 0);
return v_v_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec(v_val_86_);
v___x_88_ = lean_unbox(v_defValue_82_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(lean_object* v_opts_89_, lean_object* v_opt_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_89_, v_opt_90_);
lean_dec_ref(v_opt_90_);
lean_dec_ref(v_opts_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_executeReservedNameAction___lam__0___closed__0));
v___x_95_ = l_Lean_stringToMessageData(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0(lean_object* v_name_96_, lean_object* v_x_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l_Lean_executeReservedNameAction___lam__0___closed__1, &l_Lean_executeReservedNameAction___lam__0___closed__1_once, _init_l_Lean_executeReservedNameAction___lam__0___closed__1);
v___x_102_ = l_Lean_MessageData_ofName(v_name_96_);
v___x_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___lam__0___boxed(lean_object* v_name_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_executeReservedNameAction___lam__0(v_name_105_, v_x_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec_ref(v_x_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(lean_object* v_opts_111_, lean_object* v_opt_112_){
_start:
{
lean_object* v_name_113_; lean_object* v_defValue_114_; lean_object* v_map_115_; lean_object* v___x_116_; 
v_name_113_ = lean_ctor_get(v_opt_112_, 0);
v_defValue_114_ = lean_ctor_get(v_opt_112_, 1);
v_map_115_ = lean_ctor_get(v_opts_111_, 0);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_115_, v_name_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_inc(v_defValue_114_);
return v_defValue_114_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_116_, 1);
if (lean_obj_tag(v_val_117_) == 3)
{
lean_object* v_v_118_; 
v_v_118_ = lean_ctor_get(v_val_117_, 0);
lean_inc(v_v_118_);
lean_dec_ref_known(v_val_117_, 1);
return v_v_118_;
}
else
{
lean_dec(v_val_117_);
lean_inc(v_defValue_114_);
return v_defValue_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(lean_object* v_opts_119_, lean_object* v_opt_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_119_, v_opt_120_);
lean_dec_ref(v_opt_120_);
lean_dec_ref(v_opts_119_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
lean_ctor_set(v___x_127_, 9, v___x_125_);
lean_ctor_set(v___x_127_, 10, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4(void){
_start:
{
size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3);
v___x_136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_132_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
lean_ctor_set_usize(v___x_136_, 4, v___x_131_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(1);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_toCold_146_; lean_object* v_env_147_; lean_object* v_options_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_toCold_146_ = lean_ctor_get(v___y_142_, 0);
v_env_147_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_147_);
lean_dec(v___x_145_);
v_options_148_ = lean_ctor_get(v_toCold_146_, 2);
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_148_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v_env_147_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set(v___x_151_, 3, v_options_148_);
v___x_152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_msgData_141_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object* v_msgData_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t v_sz_159_, size_t v_i_160_, lean_object* v_bs_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_lt(v_i_160_, v_sz_159_);
if (v___x_162_ == 0)
{
return v_bs_161_;
}
else
{
lean_object* v_v_163_; lean_object* v_msg_164_; lean_object* v___x_165_; lean_object* v_bs_x27_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v_v_163_ = lean_array_uget_borrowed(v_bs_161_, v_i_160_);
v_msg_164_ = lean_ctor_get(v_v_163_, 1);
lean_inc_ref(v_msg_164_);
v___x_165_ = lean_unsigned_to_nat(0u);
v_bs_x27_166_ = lean_array_uset(v_bs_161_, v_i_160_, v___x_165_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_160_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_166_, v_i_160_, v_msg_164_);
v_i_160_ = v___x_168_;
v_bs_161_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_171_, lean_object* v_i_172_, lean_object* v_bs_173_){
_start:
{
size_t v_sz_boxed_174_; size_t v_i_boxed_175_; lean_object* v_res_176_; 
v_sz_boxed_174_ = lean_unbox_usize(v_sz_171_);
lean_dec(v_sz_171_);
v_i_boxed_175_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_res_176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_boxed_174_, v_i_boxed_175_, v_bs_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_oldTraces_177_, lean_object* v_data_178_, lean_object* v_ref_179_, lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_toCold_184_; lean_object* v_currRecDepth_185_; lean_object* v_ref_186_; uint8_t v_diag_187_; uint8_t v_suppressElabErrors_188_; lean_object* v___x_189_; lean_object* v_traceState_190_; lean_object* v_traces_191_; lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v___x_194_; size_t v_sz_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v_msg_198_; lean_object* v___x_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_237_; 
v_toCold_184_ = lean_ctor_get(v___y_181_, 0);
v_currRecDepth_185_ = lean_ctor_get(v___y_181_, 1);
v_ref_186_ = lean_ctor_get(v___y_181_, 2);
v_diag_187_ = lean_ctor_get_uint8(v___y_181_, sizeof(void*)*3);
v_suppressElabErrors_188_ = lean_ctor_get_uint8(v___y_181_, sizeof(void*)*3 + 1);
v___x_189_ = lean_st_ref_get(v___y_182_);
v_traceState_190_ = lean_ctor_get(v___x_189_, 4);
lean_inc_ref(v_traceState_190_);
lean_dec(v___x_189_);
v_traces_191_ = lean_ctor_get(v_traceState_190_, 0);
lean_inc_ref(v_traces_191_);
lean_dec_ref(v_traceState_190_);
v_ref_192_ = l_Lean_replaceRef(v_ref_179_, v_ref_186_);
lean_inc(v_currRecDepth_185_);
lean_inc_ref(v_toCold_184_);
v___x_193_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_193_, 0, v_toCold_184_);
lean_ctor_set(v___x_193_, 1, v_currRecDepth_185_);
lean_ctor_set(v___x_193_, 2, v_ref_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*3, v_diag_187_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*3 + 1, v_suppressElabErrors_188_);
v___x_194_ = l_Lean_PersistentArray_toArray___redArg(v_traces_191_);
lean_dec_ref(v_traces_191_);
v_sz_195_ = lean_array_size(v___x_194_);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_195_, v___x_196_, v___x_194_);
v_msg_198_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_198_, 0, v_data_178_);
lean_ctor_set(v_msg_198_, 1, v_msg_180_);
lean_ctor_set(v_msg_198_, 2, v___x_197_);
v___x_199_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_198_, v___x_193_, v___y_182_);
lean_dec_ref_known(v___x_193_, 3);
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_237_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_237_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_237_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v_traceState_205_; lean_object* v_env_206_; lean_object* v_nextMacroScope_207_; lean_object* v_ngen_208_; lean_object* v_auxDeclNGen_209_; lean_object* v_cache_210_; lean_object* v_messages_211_; lean_object* v_infoState_212_; lean_object* v_snapshotTasks_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_236_; 
v___x_204_ = lean_st_ref_take(v___y_182_);
v_traceState_205_ = lean_ctor_get(v___x_204_, 4);
v_env_206_ = lean_ctor_get(v___x_204_, 0);
v_nextMacroScope_207_ = lean_ctor_get(v___x_204_, 1);
v_ngen_208_ = lean_ctor_get(v___x_204_, 2);
v_auxDeclNGen_209_ = lean_ctor_get(v___x_204_, 3);
v_cache_210_ = lean_ctor_get(v___x_204_, 5);
v_messages_211_ = lean_ctor_get(v___x_204_, 6);
v_infoState_212_ = lean_ctor_get(v___x_204_, 7);
v_snapshotTasks_213_ = lean_ctor_get(v___x_204_, 8);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_236_ == 0)
{
v___x_215_ = v___x_204_;
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snapshotTasks_213_);
lean_inc(v_infoState_212_);
lean_inc(v_messages_211_);
lean_inc(v_cache_210_);
lean_inc(v_traceState_205_);
lean_inc(v_auxDeclNGen_209_);
lean_inc(v_ngen_208_);
lean_inc(v_nextMacroScope_207_);
lean_inc(v_env_206_);
lean_dec(v___x_204_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint64_t v_tid_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_234_; 
v_tid_217_ = lean_ctor_get_uint64(v_traceState_205_, sizeof(void*)*1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_traceState_205_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v_traceState_205_, 0);
lean_dec(v_unused_235_);
v___x_219_ = v_traceState_205_;
v_isShared_220_ = v_isSharedCheck_234_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_traceState_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_234_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_ref_179_);
lean_ctor_set(v___x_221_, 1, v_a_200_);
v___x_222_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_177_, v___x_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_222_);
lean_ctor_set_uint64(v_reuseFailAlloc_233_, sizeof(void*)*1, v_tid_217_);
v___x_224_ = v_reuseFailAlloc_233_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_226_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 4, v___x_224_);
v___x_226_ = v___x_215_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_env_206_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_nextMacroScope_207_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_ngen_208_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_auxDeclNGen_209_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_cache_210_);
lean_ctor_set(v_reuseFailAlloc_232_, 6, v_messages_211_);
lean_ctor_set(v_reuseFailAlloc_232_, 7, v_infoState_212_);
lean_ctor_set(v_reuseFailAlloc_232_, 8, v_snapshotTasks_213_);
v___x_226_ = v_reuseFailAlloc_232_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = lean_st_ref_put(v___y_182_, v___x_226_);
v___x_228_ = lean_box(0);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_228_);
v___x_230_ = v___x_202_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_238_, lean_object* v_data_239_, lean_object* v_ref_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_238_, v_data_239_, v_ref_240_, v_msg_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_a_248_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v_x_246_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v_x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 1);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v_x_246_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v_x_246_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 0);
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_264_);
return v_res_266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_267_){
_start:
{
if (lean_obj_tag(v_e_267_) == 0)
{
uint8_t v___x_268_; 
v___x_268_ = 2;
return v___x_268_;
}
else
{
lean_object* v_a_269_; uint8_t v___x_270_; 
v_a_269_ = lean_ctor_get(v_e_267_, 0);
v___x_270_ = lean_unbox(v_a_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_273_);
lean_dec_ref(v_e_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_276_; double v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_float_of_nat(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_281_; double v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1000u);
v___x_282_ = lean_float_of_nat(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_283_, uint8_t v_collapsed_284_, lean_object* v_tag_285_, lean_object* v_opts_286_, uint8_t v_clsEnabled_287_, lean_object* v_oldTraces_288_, lean_object* v_msg_289_, lean_object* v_resStartStop_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v_data_299_; lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___y_315_; lean_object* v_a_316_; uint8_t v___y_331_; double v___y_362_; 
v_fst_294_ = lean_ctor_get(v_resStartStop_290_, 0);
lean_inc(v_fst_294_);
v_snd_295_ = lean_ctor_get(v_resStartStop_290_, 1);
lean_inc(v_snd_295_);
lean_dec_ref(v_resStartStop_290_);
v_fst_310_ = lean_ctor_get(v_snd_295_, 0);
lean_inc(v_fst_310_);
v_snd_311_ = lean_ctor_get(v_snd_295_, 1);
lean_inc(v_snd_311_);
lean_dec(v_snd_295_);
v___x_312_ = l_Lean_trace_profiler;
v___x_313_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_286_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_331_ = v___x_313_;
goto v___jp_330_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = l_Lean_trace_profiler_useHeartbeats;
v___x_368_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_286_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; double v___x_371_; double v___x_372_; double v___x_373_; 
v___x_369_ = l_Lean_trace_profiler_threshold;
v___x_370_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_286_, v___x_369_);
v___x_371_ = lean_float_of_nat(v___x_370_);
v___x_372_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_373_ = lean_float_div(v___x_371_, v___x_372_);
v___y_362_ = v___x_373_;
goto v___jp_361_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; double v___x_376_; 
v___x_374_ = l_Lean_trace_profiler_threshold;
v___x_375_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_286_, v___x_374_);
v___x_376_ = lean_float_of_nat(v___x_375_);
v___y_362_ = v___x_376_;
goto v___jp_361_;
}
}
v___jp_296_:
{
lean_object* v___x_300_; 
lean_inc(v___y_298_);
v___x_300_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_288_, v_data_299_, v___y_298_, v___y_297_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_301_; 
lean_dec_ref_known(v___x_300_, 1);
v___x_301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_294_);
return v___x_301_;
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_fst_294_);
v_a_302_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_300_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
v___jp_314_:
{
uint8_t v_result_317_; lean_object* v___x_318_; lean_object* v___x_319_; double v___x_320_; lean_object* v_data_321_; 
v_result_317_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_294_);
v___x_318_ = lean_box(v_result_317_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
v___x_320_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
lean_inc_ref(v_tag_285_);
lean_inc_ref(v___x_319_);
lean_inc(v_cls_283_);
v_data_321_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_321_, 0, v_cls_283_);
lean_ctor_set(v_data_321_, 1, v___x_319_);
lean_ctor_set(v_data_321_, 2, v_tag_285_);
lean_ctor_set_float(v_data_321_, sizeof(void*)*3, v___x_320_);
lean_ctor_set_float(v_data_321_, sizeof(void*)*3 + 8, v___x_320_);
lean_ctor_set_uint8(v_data_321_, sizeof(void*)*3 + 16, v_collapsed_284_);
if (v___x_313_ == 0)
{
lean_dec_ref_known(v___x_319_, 1);
lean_dec(v_snd_311_);
lean_dec(v_fst_310_);
lean_dec_ref(v_tag_285_);
lean_dec(v_cls_283_);
v___y_297_ = v_a_316_;
v___y_298_ = v___y_315_;
v_data_299_ = v_data_321_;
goto v___jp_296_;
}
else
{
lean_object* v_data_322_; double v___x_323_; double v___x_324_; 
lean_dec_ref_known(v_data_321_, 3);
v_data_322_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_322_, 0, v_cls_283_);
lean_ctor_set(v_data_322_, 1, v___x_319_);
lean_ctor_set(v_data_322_, 2, v_tag_285_);
v___x_323_ = lean_unbox_float(v_fst_310_);
lean_dec(v_fst_310_);
lean_ctor_set_float(v_data_322_, sizeof(void*)*3, v___x_323_);
v___x_324_ = lean_unbox_float(v_snd_311_);
lean_dec(v_snd_311_);
lean_ctor_set_float(v_data_322_, sizeof(void*)*3 + 8, v___x_324_);
lean_ctor_set_uint8(v_data_322_, sizeof(void*)*3 + 16, v_collapsed_284_);
v___y_297_ = v_a_316_;
v___y_298_ = v___y_315_;
v_data_299_ = v_data_322_;
goto v___jp_296_;
}
}
v___jp_325_:
{
lean_object* v_ref_326_; lean_object* v___x_327_; 
v_ref_326_ = lean_ctor_get(v___y_291_, 2);
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
lean_inc(v_fst_294_);
v___x_327_ = lean_apply_4(v_msg_289_, v_fst_294_, v___y_291_, v___y_292_, lean_box(0));
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___y_315_ = v_ref_326_;
v_a_316_ = v_a_328_;
goto v___jp_314_;
}
else
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
v___y_315_ = v_ref_326_;
v_a_316_ = v___x_329_;
goto v___jp_314_;
}
}
v___jp_330_:
{
if (v_clsEnabled_287_ == 0)
{
if (v___y_331_ == 0)
{
lean_object* v___x_332_; lean_object* v_traceState_333_; lean_object* v_env_334_; lean_object* v_nextMacroScope_335_; lean_object* v_ngen_336_; lean_object* v_auxDeclNGen_337_; lean_object* v_cache_338_; lean_object* v_messages_339_; lean_object* v_infoState_340_; lean_object* v_snapshotTasks_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_snd_311_);
lean_dec(v_fst_310_);
lean_dec_ref(v_msg_289_);
lean_dec_ref(v_tag_285_);
lean_dec(v_cls_283_);
v___x_332_ = lean_st_ref_take(v___y_292_);
v_traceState_333_ = lean_ctor_get(v___x_332_, 4);
v_env_334_ = lean_ctor_get(v___x_332_, 0);
v_nextMacroScope_335_ = lean_ctor_get(v___x_332_, 1);
v_ngen_336_ = lean_ctor_get(v___x_332_, 2);
v_auxDeclNGen_337_ = lean_ctor_get(v___x_332_, 3);
v_cache_338_ = lean_ctor_get(v___x_332_, 5);
v_messages_339_ = lean_ctor_get(v___x_332_, 6);
v_infoState_340_ = lean_ctor_get(v___x_332_, 7);
v_snapshotTasks_341_ = lean_ctor_get(v___x_332_, 8);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_360_ == 0)
{
v___x_343_ = v___x_332_;
v_isShared_344_ = v_isSharedCheck_360_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snapshotTasks_341_);
lean_inc(v_infoState_340_);
lean_inc(v_messages_339_);
lean_inc(v_cache_338_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_337_);
lean_inc(v_ngen_336_);
lean_inc(v_nextMacroScope_335_);
lean_inc(v_env_334_);
lean_dec(v___x_332_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_360_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint64_t v_tid_345_; lean_object* v_traces_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_359_; 
v_tid_345_ = lean_ctor_get_uint64(v_traceState_333_, sizeof(void*)*1);
v_traces_346_ = lean_ctor_get(v_traceState_333_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_traceState_333_);
if (v_isSharedCheck_359_ == 0)
{
v___x_348_ = v_traceState_333_;
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_traces_346_);
lean_dec(v_traceState_333_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_288_, v_traces_346_);
lean_dec_ref(v_traces_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_350_);
lean_ctor_set_uint64(v_reuseFailAlloc_358_, sizeof(void*)*1, v_tid_345_);
v___x_352_ = v_reuseFailAlloc_358_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 4, v___x_352_);
v___x_354_ = v___x_343_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_env_334_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_nextMacroScope_335_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_ngen_336_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_auxDeclNGen_337_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v_cache_338_);
lean_ctor_set(v_reuseFailAlloc_357_, 6, v_messages_339_);
lean_ctor_set(v_reuseFailAlloc_357_, 7, v_infoState_340_);
lean_ctor_set(v_reuseFailAlloc_357_, 8, v_snapshotTasks_341_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_st_ref_put(v___y_292_, v___x_354_);
v___x_356_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_294_);
return v___x_356_;
}
}
}
}
}
else
{
goto v___jp_325_;
}
}
else
{
goto v___jp_325_;
}
}
v___jp_361_:
{
double v___x_363_; double v___x_364_; double v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_unbox_float(v_snd_311_);
v___x_364_ = lean_unbox_float(v_fst_310_);
v___x_365_ = lean_float_sub(v___x_363_, v___x_364_);
v___x_366_ = lean_float_decLt(v___y_362_, v___x_365_);
v___y_331_ = v___x_366_;
goto v___jp_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_377_, lean_object* v_collapsed_378_, lean_object* v_tag_379_, lean_object* v_opts_380_, lean_object* v_clsEnabled_381_, lean_object* v_oldTraces_382_, lean_object* v_msg_383_, lean_object* v_resStartStop_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v_collapsed_boxed_388_; uint8_t v_clsEnabled_boxed_389_; lean_object* v_res_390_; 
v_collapsed_boxed_388_ = lean_unbox(v_collapsed_378_);
v_clsEnabled_boxed_389_ = lean_unbox(v_clsEnabled_381_);
v_res_390_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_377_, v_collapsed_boxed_388_, v_tag_379_, v_opts_380_, v_clsEnabled_boxed_389_, v_oldTraces_382_, v_msg_383_, v_resStartStop_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec_ref(v_opts_380_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_391_, lean_object* v_as_392_, size_t v_i_393_, size_t v_stop_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_eq(v_i_393_, v_stop_394_);
if (v___x_398_ == 0)
{
lean_object* v___x_5256__overap_399_; lean_object* v___x_400_; 
v___x_5256__overap_399_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
lean_inc(v___x_5256__overap_399_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc(v_name_391_);
v___x_400_ = lean_apply_4(v___x_5256__overap_399_, v_name_391_, v___y_395_, v___y_396_, lean_box(0));
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_412_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint8_t v___x_405_; 
v___x_405_ = lean_unbox(v_a_401_);
if (v___x_405_ == 0)
{
size_t v___x_406_; size_t v___x_407_; 
lean_del_object(v___x_403_);
lean_dec(v_a_401_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_393_, v___x_406_);
v_i_393_ = v___x_407_;
goto _start;
}
else
{
lean_object* v___x_410_; 
lean_dec(v_name_391_);
if (v_isShared_404_ == 0)
{
v___x_410_ = v___x_403_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_401_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_dec(v_name_391_);
return v___x_400_;
}
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_name_391_);
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_416_, lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
size_t v_i_boxed_423_; size_t v_stop_boxed_424_; lean_object* v_res_425_; 
v_i_boxed_423_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_424_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_416_, v_as_417_, v_i_boxed_423_, v_stop_boxed_424_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v_as_417_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_434_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_435_ = l_Lean_Name_append(v___x_434_, v___x_433_);
return v___x_435_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_436_; double v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1000000000u);
v___x_437_ = lean_float_of_nat(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_toCold_442_; lean_object* v_options_443_; lean_object* v_inheritedTraceOptions_444_; uint8_t v_hasTrace_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___y_449_; 
v_toCold_442_ = lean_ctor_get(v_a_439_, 0);
v_options_443_ = lean_ctor_get(v_toCold_442_, 2);
v_inheritedTraceOptions_444_ = lean_ctor_get(v_toCold_442_, 11);
v_hasTrace_445_ = lean_ctor_get_uint8(v_options_443_, sizeof(void*)*1);
v___x_446_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_447_ = lean_box(0);
if (v_hasTrace_445_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_st_ref_get(v___x_446_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_array_get_size(v___x_466_);
v___x_469_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v___x_466_);
lean_dec(v_name_438_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_447_);
return v___x_470_;
}
else
{
if (v___x_469_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v___x_466_);
lean_dec(v_name_438_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_447_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_468_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_438_, v___x_466_, v___x_472_, v___x_473_, v_a_439_, v_a_440_);
lean_dec(v___x_466_);
v___y_449_ = v___x_474_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_a_483_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v_a_498_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v_a_504_; lean_object* v___y_514_; lean_object* v___y_515_; uint8_t v_a_516_; 
lean_inc(v_name_438_);
v___f_475_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_475_, 0, v_name_438_);
v___x_476_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_477_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_478_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_444_, v_options_443_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = l_Lean_trace_profiler;
v___x_561_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_443_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
lean_dec_ref(v___f_475_);
v___x_562_ = lean_st_ref_get(v___x_446_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get_size(v___x_562_);
v___x_565_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v___x_562_);
lean_dec(v_name_438_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_447_);
return v___x_566_;
}
else
{
if (v___x_565_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v___x_562_);
lean_dec(v_name_438_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_447_);
return v___x_567_;
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_564_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_438_, v___x_562_, v___x_568_, v___x_569_, v_a_439_, v_a_440_);
lean_dec(v___x_562_);
v___y_449_ = v___x_570_;
goto v___jp_448_;
}
}
}
else
{
goto v___jp_519_;
}
}
else
{
goto v___jp_519_;
}
v___jp_480_:
{
lean_object* v___x_484_; double v___x_485_; double v___x_486_; double v___x_487_; double v___x_488_; double v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_484_ = lean_io_mono_nanos_now();
v___x_485_ = lean_float_of_nat(v___y_482_);
v___x_486_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_487_ = lean_float_div(v___x_485_, v___x_486_);
v___x_488_ = lean_float_of_nat(v___x_484_);
v___x_489_ = lean_float_div(v___x_488_, v___x_486_);
v___x_490_ = lean_box_float(v___x_487_);
v___x_491_ = lean_box_float(v___x_489_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_a_483_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_476_, v_hasTrace_445_, v___x_477_, v_options_443_, v___x_479_, v___y_481_, v___f_475_, v___x_493_, v_a_439_, v_a_440_);
v___y_449_ = v___x_494_;
goto v___jp_448_;
}
v___jp_495_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(v_a_498_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___y_481_ = v___y_497_;
v___y_482_ = v___y_496_;
v_a_483_ = v___x_500_;
goto v___jp_480_;
}
v___jp_501_:
{
lean_object* v___x_505_; double v___x_506_; double v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_505_ = lean_io_get_num_heartbeats();
v___x_506_ = lean_float_of_nat(v___y_502_);
v___x_507_ = lean_float_of_nat(v___x_505_);
v___x_508_ = lean_box_float(v___x_506_);
v___x_509_ = lean_box_float(v___x_507_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_a_504_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_476_, v_hasTrace_445_, v___x_477_, v_options_443_, v___x_479_, v___y_503_, v___f_475_, v___x_511_, v_a_439_, v_a_440_);
v___y_449_ = v___x_512_;
goto v___jp_448_;
}
v___jp_513_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_box(v_a_516_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___y_502_ = v___y_514_;
v___y_503_ = v___y_515_;
v_a_504_ = v___x_518_;
goto v___jp_501_;
}
v___jp_519_:
{
lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_440_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_trace_profiler_useHeartbeats;
v___x_523_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_443_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_524_ = lean_io_mono_nanos_now();
v___x_525_ = lean_st_ref_get(v___x_446_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_array_get_size(v___x_525_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_525_);
lean_dec(v_name_438_);
v___y_496_ = v___x_524_;
v___y_497_ = v_a_521_;
v_a_498_ = v___x_528_;
goto v___jp_495_;
}
else
{
if (v___x_528_ == 0)
{
lean_dec(v___x_525_);
lean_dec(v_name_438_);
v___y_496_ = v___x_524_;
v___y_497_ = v_a_521_;
v_a_498_ = v___x_528_;
goto v___jp_495_;
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_438_, v___x_525_, v___x_529_, v___x_530_, v_a_439_, v_a_440_);
lean_dec(v___x_525_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; uint8_t v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = lean_unbox(v_a_532_);
lean_dec(v_a_532_);
v___y_496_ = v___x_524_;
v___y_497_ = v_a_521_;
v_a_498_ = v___x_533_;
goto v___jp_495_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_531_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 0);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
v___y_481_ = v_a_521_;
v___y_482_ = v___x_524_;
v_a_483_ = v___x_539_;
goto v___jp_480_;
}
}
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_542_ = lean_io_get_num_heartbeats();
v___x_543_ = lean_st_ref_get(v___x_446_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v___x_543_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v___x_543_);
lean_dec(v_name_438_);
v___y_514_ = v___x_542_;
v___y_515_ = v_a_521_;
v_a_516_ = v___x_546_;
goto v___jp_513_;
}
else
{
if (v___x_546_ == 0)
{
lean_dec(v___x_543_);
lean_dec(v_name_438_);
v___y_514_ = v___x_542_;
v___y_515_ = v_a_521_;
v_a_516_ = v___x_546_;
goto v___jp_513_;
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_545_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_438_, v___x_543_, v___x_547_, v___x_548_, v_a_439_, v_a_440_);
lean_dec(v___x_543_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; uint8_t v___x_551_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_unbox(v_a_550_);
lean_dec(v_a_550_);
v___y_514_ = v___x_542_;
v___y_515_ = v_a_521_;
v_a_516_ = v___x_551_;
goto v___jp_513_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_549_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 0);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_502_ = v___x_542_;
v___y_503_ = v_a_521_;
v_a_504_ = v___x_557_;
goto v___jp_501_;
}
}
}
}
}
}
}
}
v___jp_448_:
{
if (lean_obj_tag(v___y_449_) == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_isSharedCheck_456_ = !lean_is_exclusive(v___y_449_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___y_449_, 0);
lean_dec(v_unused_457_);
v___x_451_ = v___y_449_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___y_449_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_447_);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___y_449_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___y_449_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___y_449_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___y_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_executeReservedNameAction(v_name_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_576_, lean_object* v_x_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_577_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_582_, v_x_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_587_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_595_, uint8_t v___y_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 1)
{
lean_object* v_pre_598_; 
v_pre_598_ = lean_ctor_get(v_x_597_, 0);
switch(lean_obj_tag(v_pre_598_))
{
case 1:
{
lean_object* v_pre_599_; 
v_pre_599_ = lean_ctor_get(v_pre_598_, 0);
switch(lean_obj_tag(v_pre_599_))
{
case 0:
{
lean_object* v_str_600_; lean_object* v_str_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_str_600_ = lean_ctor_get(v_x_597_, 1);
v_str_601_ = lean_ctor_get(v_pre_598_, 1);
v___x_602_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_603_ = lean_string_dec_eq(v_str_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_605_ = lean_string_dec_eq(v_str_601_, v___x_604_);
if (v___x_605_ == 0)
{
return v___x_605_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_607_ = lean_string_dec_eq(v_str_600_, v___x_606_);
if (v___x_607_ == 0)
{
return v___x_607_;
}
else
{
return v_suppressElabErrors_595_;
}
}
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_609_ = lean_string_dec_eq(v_str_600_, v___x_608_);
if (v___x_609_ == 0)
{
return v___x_609_;
}
else
{
return v_suppressElabErrors_595_;
}
}
}
case 1:
{
lean_object* v_pre_610_; 
v_pre_610_ = lean_ctor_get(v_pre_599_, 0);
if (lean_obj_tag(v_pre_610_) == 0)
{
lean_object* v_str_611_; lean_object* v_str_612_; lean_object* v_str_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_str_611_ = lean_ctor_get(v_x_597_, 1);
v_str_612_ = lean_ctor_get(v_pre_598_, 1);
v_str_613_ = lean_ctor_get(v_pre_599_, 1);
v___x_614_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_615_ = lean_string_dec_eq(v_str_613_, v___x_614_);
if (v___x_615_ == 0)
{
return v___x_615_;
}
else
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_617_ = lean_string_dec_eq(v_str_612_, v___x_616_);
if (v___x_617_ == 0)
{
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_619_ = lean_string_dec_eq(v_str_611_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
return v_suppressElabErrors_595_;
}
}
}
}
else
{
return v___y_596_;
}
}
default: 
{
return v___y_596_;
}
}
}
case 0:
{
lean_object* v_str_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_str_620_ = lean_ctor_get(v_x_597_, 1);
v___x_621_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_622_ = lean_string_dec_eq(v_str_620_, v___x_621_);
if (v___x_622_ == 0)
{
return v___x_622_;
}
else
{
return v_suppressElabErrors_595_;
}
}
default: 
{
return v___y_596_;
}
}
}
else
{
return v___y_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_623_, lean_object* v___y_624_, lean_object* v_x_625_){
_start:
{
uint8_t v_suppressElabErrors_boxed_626_; uint8_t v___y_4813__boxed_627_; uint8_t v_res_628_; lean_object* v_r_629_; 
v_suppressElabErrors_boxed_626_ = lean_unbox(v_suppressElabErrors_623_);
v___y_4813__boxed_627_ = lean_unbox(v___y_624_);
v_res_628_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_626_, v___y_4813__boxed_627_, v_x_625_);
lean_dec(v_x_625_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_630_, lean_object* v_msgData_631_, uint8_t v_severity_632_, uint8_t v_isSilent_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_675_; uint8_t v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; lean_object* v___y_707_; lean_object* v___y_711_; uint8_t v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; uint8_t v___x_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; uint8_t v___y_732_; uint8_t v___x_748_; 
v___x_722_ = 2;
v___x_748_ = l_Lean_instBEqMessageSeverity_beq(v_severity_632_, v___x_722_);
if (v___x_748_ == 0)
{
v___y_732_ = v___x_748_;
goto v___jp_731_;
}
else
{
uint8_t v___x_749_; 
lean_inc_ref(v_msgData_631_);
v___x_749_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_631_);
v___y_732_ = v___x_749_;
goto v___jp_731_;
}
v___jp_637_:
{
lean_object* v___x_647_; lean_object* v_toCold_648_; lean_object* v_currNamespace_649_; lean_object* v_openDecls_650_; lean_object* v_env_651_; lean_object* v_nextMacroScope_652_; lean_object* v_ngen_653_; lean_object* v_auxDeclNGen_654_; lean_object* v_traceState_655_; lean_object* v_cache_656_; lean_object* v_messages_657_; lean_object* v_infoState_658_; lean_object* v_snapshotTasks_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_673_; 
v___x_647_ = lean_st_ref_take(v___y_646_);
v_toCold_648_ = lean_ctor_get(v___y_645_, 0);
v_currNamespace_649_ = lean_ctor_get(v_toCold_648_, 4);
v_openDecls_650_ = lean_ctor_get(v_toCold_648_, 5);
v_env_651_ = lean_ctor_get(v___x_647_, 0);
v_nextMacroScope_652_ = lean_ctor_get(v___x_647_, 1);
v_ngen_653_ = lean_ctor_get(v___x_647_, 2);
v_auxDeclNGen_654_ = lean_ctor_get(v___x_647_, 3);
v_traceState_655_ = lean_ctor_get(v___x_647_, 4);
v_cache_656_ = lean_ctor_get(v___x_647_, 5);
v_messages_657_ = lean_ctor_get(v___x_647_, 6);
v_infoState_658_ = lean_ctor_get(v___x_647_, 7);
v_snapshotTasks_659_ = lean_ctor_get(v___x_647_, 8);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_673_ == 0)
{
v___x_661_ = v___x_647_;
v_isShared_662_ = v_isSharedCheck_673_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_snapshotTasks_659_);
lean_inc(v_infoState_658_);
lean_inc(v_messages_657_);
lean_inc(v_cache_656_);
lean_inc(v_traceState_655_);
lean_inc(v_auxDeclNGen_654_);
lean_inc(v_ngen_653_);
lean_inc(v_nextMacroScope_652_);
lean_inc(v_env_651_);
lean_dec(v___x_647_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_673_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc(v_openDecls_650_);
lean_inc(v_currNamespace_649_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_currNamespace_649_);
lean_ctor_set(v___x_663_, 1, v_openDecls_650_);
v___x_664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___y_642_);
lean_inc_ref(v___y_643_);
lean_inc_ref(v___y_641_);
v___x_665_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_665_, 0, v___y_641_);
lean_ctor_set(v___x_665_, 1, v___y_644_);
lean_ctor_set(v___x_665_, 2, v___y_640_);
lean_ctor_set(v___x_665_, 3, v___y_643_);
lean_ctor_set(v___x_665_, 4, v___x_664_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5, v___y_638_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5 + 1, v___y_639_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*5 + 2, v_isSilent_633_);
v___x_666_ = l_Lean_MessageLog_add(v___x_665_, v_messages_657_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 6, v___x_666_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_env_651_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_nextMacroScope_652_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ngen_653_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_auxDeclNGen_654_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_traceState_655_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v_cache_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_672_, 7, v_infoState_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 8, v_snapshotTasks_659_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_st_ref_put(v___y_646_, v___x_668_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
v___jp_674_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_698_; 
v___x_683_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_631_);
v___x_684_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_683_, v___y_634_, v___y_635_);
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_698_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_698_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_698_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_inc_ref_n(v___y_677_, 2);
v___x_689_ = l_Lean_FileMap_toPosition(v___y_677_, v___y_678_);
lean_dec(v___y_678_);
v___x_690_ = l_Lean_FileMap_toPosition(v___y_677_, v___y_682_);
lean_dec(v___y_682_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_680_ == 0)
{
lean_del_object(v___x_687_);
lean_dec_ref(v___y_675_);
v___y_638_ = v___y_676_;
v___y_639_ = v___y_679_;
v___y_640_ = v___x_691_;
v___y_641_ = v___y_681_;
v___y_642_ = v_a_685_;
v___y_643_ = v___x_692_;
v___y_644_ = v___x_689_;
v___y_645_ = v___y_634_;
v___y_646_ = v___y_635_;
goto v___jp_637_;
}
else
{
uint8_t v___x_693_; 
lean_inc(v_a_685_);
v___x_693_ = l_Lean_MessageData_hasTag(v___y_675_, v_a_685_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec_ref_known(v___x_691_, 1);
lean_dec_ref(v___x_689_);
lean_dec(v_a_685_);
v___x_694_ = lean_box(0);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_694_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_del_object(v___x_687_);
v___y_638_ = v___y_676_;
v___y_639_ = v___y_679_;
v___y_640_ = v___x_691_;
v___y_641_ = v___y_681_;
v___y_642_ = v_a_685_;
v___y_643_ = v___x_692_;
v___y_644_ = v___x_689_;
v___y_645_ = v___y_634_;
v___y_646_ = v___y_635_;
goto v___jp_637_;
}
}
}
}
v___jp_699_:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Syntax_getTailPos_x3f(v___y_704_, v___y_702_);
lean_dec(v___y_704_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_inc(v___y_707_);
v___y_675_ = v___y_700_;
v___y_676_ = v___y_702_;
v___y_677_ = v___y_701_;
v___y_678_ = v___y_707_;
v___y_679_ = v___y_703_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_705_;
v___y_682_ = v___y_707_;
goto v___jp_674_;
}
else
{
lean_object* v_val_709_; 
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_708_, 1);
v___y_675_ = v___y_700_;
v___y_676_ = v___y_702_;
v___y_677_ = v___y_701_;
v___y_678_ = v___y_707_;
v___y_679_ = v___y_703_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_705_;
v___y_682_ = v_val_709_;
goto v___jp_674_;
}
}
v___jp_710_:
{
lean_object* v_ref_718_; lean_object* v___x_719_; 
v_ref_718_ = l_Lean_replaceRef(v_ref_630_, v___y_714_);
v___x_719_ = l_Lean_Syntax_getPos_x3f(v_ref_718_, v___y_712_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_unsigned_to_nat(0u);
v___y_700_ = v___y_711_;
v___y_701_ = v___y_713_;
v___y_702_ = v___y_712_;
v___y_703_ = v___y_717_;
v___y_704_ = v_ref_718_;
v___y_705_ = v___y_716_;
v___y_706_ = v___y_715_;
v___y_707_ = v___x_720_;
goto v___jp_699_;
}
else
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_719_, 1);
v___y_700_ = v___y_711_;
v___y_701_ = v___y_713_;
v___y_702_ = v___y_712_;
v___y_703_ = v___y_717_;
v___y_704_ = v_ref_718_;
v___y_705_ = v___y_716_;
v___y_706_ = v___y_715_;
v___y_707_ = v_val_721_;
goto v___jp_699_;
}
}
v___jp_723_:
{
if (v___y_730_ == 0)
{
v___y_711_ = v___y_725_;
v___y_712_ = v___y_727_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_729_;
v___y_716_ = v___y_726_;
v___y_717_ = v_severity_632_;
goto v___jp_710_;
}
else
{
v___y_711_ = v___y_725_;
v___y_712_ = v___y_727_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_729_;
v___y_716_ = v___y_726_;
v___y_717_ = v___x_722_;
goto v___jp_710_;
}
}
v___jp_731_:
{
if (v___y_732_ == 0)
{
lean_object* v_toCold_733_; lean_object* v_ref_734_; uint8_t v_suppressElabErrors_735_; lean_object* v_fileName_736_; lean_object* v_fileMap_737_; lean_object* v_options_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___f_741_; uint8_t v___x_742_; uint8_t v___x_743_; 
v_toCold_733_ = lean_ctor_get(v___y_634_, 0);
v_ref_734_ = lean_ctor_get(v___y_634_, 2);
v_suppressElabErrors_735_ = lean_ctor_get_uint8(v___y_634_, sizeof(void*)*3 + 1);
v_fileName_736_ = lean_ctor_get(v_toCold_733_, 0);
v_fileMap_737_ = lean_ctor_get(v_toCold_733_, 1);
v_options_738_ = lean_ctor_get(v_toCold_733_, 2);
v___x_739_ = lean_box(v_suppressElabErrors_735_);
v___x_740_ = lean_box(v___y_732_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_741_, 0, v___x_739_);
lean_closure_set(v___f_741_, 1, v___x_740_);
v___x_742_ = 1;
v___x_743_ = l_Lean_instBEqMessageSeverity_beq(v_severity_632_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_724_ = v_fileMap_737_;
v___y_725_ = v___f_741_;
v___y_726_ = v_fileName_736_;
v___y_727_ = v___y_732_;
v___y_728_ = v_ref_734_;
v___y_729_ = v_suppressElabErrors_735_;
v___y_730_ = v___x_743_;
goto v___jp_723_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = l_Lean_warningAsError;
v___x_745_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_738_, v___x_744_);
v___y_724_ = v_fileMap_737_;
v___y_725_ = v___f_741_;
v___y_726_ = v_fileName_736_;
v___y_727_ = v___y_732_;
v___y_728_ = v_ref_734_;
v___y_729_ = v_suppressElabErrors_735_;
v___y_730_ = v___x_745_;
goto v___jp_723_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_msgData_631_);
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
lean_object* v_head_802_; lean_object* v_tail_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_853_; 
v_head_802_ = lean_ctor_get(v_x_796_, 0);
v_tail_803_ = lean_ctor_get(v_x_796_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_853_ == 0)
{
v___x_805_ = v_x_796_;
v_isShared_806_ = v_isSharedCheck_853_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_tail_803_);
lean_inc(v_head_802_);
lean_dec(v_x_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_853_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v_a_813_; lean_object* v_fst_815_; lean_object* v___x_816_; lean_object* v_env_817_; uint8_t v___x_818_; uint8_t v___x_819_; 
v_fst_815_ = lean_ctor_get(v_head_802_, 0);
v___x_816_ = lean_st_ref_get(v___y_799_);
v_env_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_env_817_);
lean_dec(v___x_816_);
v___x_818_ = 1;
lean_inc(v_fst_815_);
v___x_819_ = l_Lean_Environment_contains(v_env_817_, v_fst_815_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_inc(v_fst_815_);
v___x_820_ = l_Lean_executeReservedNameAction(v_fst_815_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; lean_object* v_env_822_; uint8_t v___x_823_; 
lean_dec_ref_known(v___x_820_, 1);
v___x_821_ = lean_st_ref_get(v___y_799_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = l_Lean_Environment_containsOnBranch(v_env_822_, v_fst_815_);
lean_dec_ref(v_env_822_);
v_a_813_ = v___x_823_;
goto v___jp_812_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_852_; 
v_a_824_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_852_ == 0)
{
v___x_826_ = v___x_820_;
v_isShared_827_ = v_isSharedCheck_852_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_820_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_852_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___y_829_; uint8_t v___x_850_; 
v___x_850_ = l_Lean_Exception_isInterrupt(v_a_824_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; 
lean_inc(v_a_824_);
v___x_851_ = l_Lean_Exception_isRuntime(v_a_824_);
v___y_829_ = v___x_851_;
goto v___jp_828_;
}
else
{
v___y_829_ = v___x_850_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_826_);
v___x_830_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_795_);
v___x_831_ = l_Lean_MessageData_ofName(v_id_795_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_Exception_toMessageData(v_a_824_);
v___x_836_ = l_Lean_indentD(v___x_835_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_837_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_dec_ref_known(v___x_838_, 1);
v_a_813_ = v___x_819_;
goto v___jp_812_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_del_object(v___x_805_);
lean_dec(v_tail_803_);
lean_dec(v_head_802_);
lean_dec(v_x_797_);
lean_dec(v_id_795_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
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
lean_object* v___x_848_; 
lean_del_object(v___x_805_);
lean_dec(v_tail_803_);
lean_dec(v_head_802_);
lean_dec(v_x_797_);
lean_dec(v_id_795_);
if (v_isShared_827_ == 0)
{
v___x_848_ = v___x_826_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_824_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
else
{
goto v___jp_807_;
}
v___jp_807_:
{
lean_object* v___x_809_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_x_797_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_head_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_x_797_);
v___x_809_ = v_reuseFailAlloc_811_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v_x_796_ = v_tail_803_;
v_x_797_ = v___x_809_;
goto _start;
}
}
v___jp_812_:
{
if (v_a_813_ == 0)
{
lean_del_object(v___x_805_);
lean_dec(v_head_802_);
v_x_796_ = v_tail_803_;
goto _start;
}
else
{
goto v___jp_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_854_, v_x_855_, v_x_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v_fst_865_; uint8_t v___x_866_; 
v_head_863_ = lean_ctor_get(v_x_861_, 0);
v_tail_864_ = lean_ctor_get(v_x_861_, 1);
v_fst_865_ = lean_ctor_get(v_head_863_, 0);
v___x_866_ = l_Lean_isPrivateName(v_fst_865_);
if (v___x_866_ == 0)
{
v_x_861_ = v_tail_864_;
goto _start;
}
else
{
lean_object* v___x_868_; 
lean_inc(v_head_863_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_head_863_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_869_);
lean_dec(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = 1;
v___x_876_ = 0;
v___x_877_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_871_, v___x_875_, v___x_876_, v___y_872_, v___y_873_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_toCold_886_; lean_object* v_options_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_toCold_886_ = lean_ctor_get(v___y_884_, 0);
v_options_887_ = lean_ctor_get(v_toCold_886_, 2);
v___x_888_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_887_, v_opt_883_);
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
v_isExporting_918_ = lean_ctor_get_uint8(v_env_906_, sizeof(void*)*8);
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
lean_object* v___x_939_; lean_object* v_toCold_940_; lean_object* v_env_941_; lean_object* v_options_942_; lean_object* v_currNamespace_943_; lean_object* v_openDecls_944_; lean_object* v___x_945_; lean_object* v_env_946_; lean_object* v_res_947_; 
v___x_939_ = lean_st_ref_get(v___y_937_);
v_toCold_940_ = lean_ctor_get(v___y_936_, 0);
v_env_941_ = lean_ctor_get(v___x_939_, 0);
lean_inc_ref(v_env_941_);
lean_dec(v___x_939_);
v_options_942_ = lean_ctor_get(v_toCold_940_, 2);
v_currNamespace_943_ = lean_ctor_get(v_toCold_940_, 4);
v_openDecls_944_ = lean_ctor_get(v_toCold_940_, 5);
v___x_945_ = lean_st_ref_get(v___y_937_);
v_env_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_946_);
lean_dec(v___x_945_);
lean_inc(v_openDecls_944_);
lean_inc(v_currNamespace_943_);
v_res_947_ = l_Lean_ResolveName_resolveGlobalName(v_env_941_, v_options_942_, v_currNamespace_943_, v_openDecls_944_, v_id_934_);
if (v_enableLog_935_ == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v_env_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_res_947_);
return v___x_948_;
}
else
{
uint8_t v_isExporting_949_; 
v_isExporting_949_ = lean_ctor_get_uint8(v_env_946_, sizeof(void*)*8);
lean_dec_ref(v_env_946_);
if (v_isExporting_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_res_947_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_947_);
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
lean_ctor_set(v___x_956_, 0, v_res_947_);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_res_947_);
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
lean_dec(v_res_947_);
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
lean_ctor_set(v___x_971_, 0, v_res_947_);
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
lean_object* v_toCold_1051_; lean_object* v_currRecDepth_1052_; lean_object* v_ref_1053_; uint8_t v_diag_1054_; uint8_t v_suppressElabErrors_1055_; lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_toCold_1051_ = lean_ctor_get(v___y_1048_, 0);
v_currRecDepth_1052_ = lean_ctor_get(v___y_1048_, 1);
v_ref_1053_ = lean_ctor_get(v___y_1048_, 2);
v_diag_1054_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3);
v_suppressElabErrors_1055_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 1);
v_ref_1056_ = l_Lean_replaceRef(v_ref_1046_, v_ref_1053_);
lean_inc(v_currRecDepth_1052_);
lean_inc_ref(v_toCold_1051_);
v___x_1057_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1057_, 0, v_toCold_1051_);
lean_ctor_set(v___x_1057_, 1, v_currRecDepth_1052_);
lean_ctor_set(v___x_1057_, 2, v_ref_1056_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*3, v_diag_1054_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*3 + 1, v_suppressElabErrors_1055_);
v___x_1058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1047_, v___x_1057_, v___y_1049_);
lean_dec_ref_known(v___x_1057_, 3);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1059_, lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1059_, v_msg_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_ref_1059_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1086_, lean_object* v_declHint_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v_env_1091_; uint8_t v___x_1092_; 
v___x_1090_ = lean_st_ref_get(v___y_1088_);
v_env_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc_ref(v_env_1091_);
lean_dec(v___x_1090_);
v___x_1092_ = l_Lean_Name_isAnonymous(v_declHint_1087_);
if (v___x_1092_ == 0)
{
uint8_t v_isExporting_1093_; 
v_isExporting_1093_ = lean_ctor_get_uint8(v_env_1091_, sizeof(void*)*8);
if (v_isExporting_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_env_1091_);
lean_dec(v_declHint_1087_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_msg_1086_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
lean_inc_ref(v_env_1091_);
v___x_1095_ = l_Lean_Environment_setExporting(v_env_1091_, v___x_1092_);
lean_inc(v_declHint_1087_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = l_Lean_Environment_contains(v___x_1095_, v_declHint_1087_, v_isExporting_1093_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_env_1091_);
lean_dec(v_declHint_1087_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_msg_1086_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_c_1103_; lean_object* v___x_1104_; 
v___x_1098_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1099_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1100_ = l_Lean_Options_empty;
v___x_1101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1095_);
lean_ctor_set(v___x_1101_, 1, v___x_1098_);
lean_ctor_set(v___x_1101_, 2, v___x_1099_);
lean_ctor_set(v___x_1101_, 3, v___x_1100_);
lean_inc(v_declHint_1087_);
v___x_1102_ = l_Lean_MessageData_ofConstName(v_declHint_1087_, v___x_1092_);
v_c_1103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1103_, 0, v___x_1101_);
lean_ctor_set(v_c_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1091_, v_declHint_1087_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref(v_env_1091_);
lean_dec(v_declHint_1087_);
v___x_1105_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_c_1103_);
v___x_1107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_MessageData_note(v___x_1108_);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_msg_1086_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_val_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1147_; 
v_val_1112_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1114_ = v___x_1104_;
v_isShared_1115_ = v_isSharedCheck_1147_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_val_1112_);
lean_dec(v___x_1104_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1147_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_mod_1119_; uint8_t v___x_1120_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Lean_Environment_header(v_env_1091_);
lean_dec_ref(v_env_1091_);
v___x_1118_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1117_);
v_mod_1119_ = lean_array_get(v___x_1116_, v___x_1118_, v_val_1112_);
lean_dec(v_val_1112_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = l_Lean_isPrivateName(v_declHint_1087_);
lean_dec(v_declHint_1087_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_c_1103_);
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofName(v_mod_1119_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_note(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_msg_1086_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1130_);
v___x_1132_ = v___x_1114_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_c_1103_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofName(v_mod_1119_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_MessageData_note(v___x_1141_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_msg_1086_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1143_);
v___x_1145_ = v___x_1114_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1148_; 
lean_dec_ref(v_env_1091_);
lean_dec(v_declHint_1087_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1086_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1149_, lean_object* v_declHint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1149_, v_declHint_1150_, v___y_1151_);
lean_dec(v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1154_, lean_object* v_declHint_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1169_; 
v___x_1159_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1154_, v_declHint_1155_, v___y_1157_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = l_Lean_unknownIdentifierMessageTag;
v___x_1165_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1170_, lean_object* v_declHint_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1170_, v_declHint_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1176_, lean_object* v_msg_1177_, lean_object* v_declHint_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_a_1183_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1177_, v_declHint_1178_, v___y_1179_, v___y_1180_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1176_, v_a_1183_, v___y_1179_, v___y_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1185_, lean_object* v_msg_1186_, lean_object* v_declHint_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1185_, v_msg_1186_, v_declHint_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v_ref_1185_);
return v_res_1191_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1198_, lean_object* v_constName_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1203_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1204_ = 0;
lean_inc(v_constName_1199_);
v___x_1205_ = l_Lean_MessageData_ofConstName(v_constName_1199_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1203_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1198_, v___x_1208_, v_constName_1199_, v___y_1200_, v___y_1201_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1210_, lean_object* v_constName_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1210_, v_constName_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v_ref_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
if (lean_obj_tag(v_a_1216_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = l_List_reverse___redArg(v_a_1217_);
return v___x_1218_;
}
else
{
lean_object* v_head_1219_; lean_object* v_tail_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1231_; 
v_head_1219_ = lean_ctor_get(v_a_1216_, 0);
v_tail_1220_ = lean_ctor_get(v_a_1216_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_a_1216_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1222_ = v_a_1216_;
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_tail_1220_);
lean_inc(v_head_1219_);
lean_dec(v_a_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_snd_1224_; uint8_t v___x_1225_; 
v_snd_1224_ = lean_ctor_get(v_head_1219_, 1);
v___x_1225_ = l_List_isEmpty___redArg(v_snd_1224_);
if (v___x_1225_ == 0)
{
lean_del_object(v___x_1222_);
lean_dec(v_head_1219_);
v_a_1216_ = v_tail_1220_;
goto _start;
}
else
{
lean_object* v___x_1228_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_a_1217_);
v___x_1228_ = v___x_1222_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_head_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_a_1217_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v_a_1216_ = v_tail_1220_;
v_a_1217_ = v___x_1228_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1232_, lean_object* v_cs_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_cs_1238_; uint8_t v___x_1242_; 
v___x_1237_ = lean_box(0);
v_cs_1238_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1233_, v___x_1237_);
v___x_1242_ = l_List_isEmpty___redArg(v_cs_1238_);
if (v___x_1242_ == 0)
{
lean_dec(v_n_1232_);
goto v___jp_1239_;
}
else
{
lean_object* v_ref_1243_; lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_cs_1238_);
v_ref_1243_ = lean_ctor_get(v___y_1234_, 2);
v___x_1244_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1243_, v_n_1232_, v___y_1234_, v___y_1235_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
v___jp_1239_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1238_, v___x_1237_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1253_, lean_object* v_cs_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1253_, v_cs_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; 
lean_inc(v_n_1259_);
v___x_1263_ = l_Lean_realizeGlobalName(v_n_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1259_, v_a_1264_, v_a_1260_, v_a_1261_);
return v___x_1265_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_n_1259_);
v_a_1266_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1263_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1263_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_realizeGlobalConstCore(v_n_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1279_, lean_object* v_ref_1280_, lean_object* v_constName_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1280_, v_constName_1281_, v___y_1282_, v___y_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_ref_1287_, lean_object* v_constName_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1286_, v_ref_1287_, v_constName_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v_ref_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1293_, lean_object* v_ref_1294_, lean_object* v_msg_1295_, lean_object* v_declHint_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1294_, v_msg_1295_, v_declHint_1296_, v___y_1297_, v___y_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1301_, lean_object* v_ref_1302_, lean_object* v_msg_1303_, lean_object* v_declHint_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1301_, v_ref_1302_, v_msg_1303_, v_declHint_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v_ref_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1309_, lean_object* v_declHint_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1309_, v_declHint_1310_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1315_, lean_object* v_declHint_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1315_, v_declHint_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v_msg_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1322_, v_msg_1323_, v___y_1324_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_ref_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1328_, v_ref_1329_, v_msg_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v_ref_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1341_, v_msg_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_List_reverse___redArg(v_a_1348_);
return v___x_1349_;
}
else
{
lean_object* v_head_1350_; lean_object* v_tail_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1360_; 
v_head_1350_ = lean_ctor_get(v_a_1347_, 0);
v_tail_1351_ = lean_ctor_get(v_a_1347_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1353_ = v_a_1347_;
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_tail_1351_);
lean_inc(v_head_1350_);
lean_dec(v_a_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l_Lean_MessageData_ofExpr(v_head_1350_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_a_1348_);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1348_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
v_a_1347_ = v_tail_1351_;
v_a_1348_ = v___x_1357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
if (lean_obj_tag(v_a_1361_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_List_reverse___redArg(v_a_1362_);
return v___x_1363_;
}
else
{
lean_object* v_head_1364_; lean_object* v_tail_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1375_; 
v_head_1364_ = lean_ctor_get(v_a_1361_, 0);
v_tail_1365_ = lean_ctor_get(v_a_1361_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1361_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1367_ = v_a_1361_;
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_tail_1365_);
lean_inc(v_head_1364_);
lean_dec(v_a_1361_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Lean_mkConst(v_head_1364_, v___x_1369_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_a_1362_);
lean_ctor_set(v___x_1367_, 0, v___x_1370_);
v___x_1372_ = v___x_1367_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_a_1362_);
v___x_1372_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_a_1361_ = v_tail_1365_;
v_a_1362_ = v___x_1372_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1382_, lean_object* v_cs_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
if (lean_obj_tag(v_cs_1383_) == 1)
{
lean_object* v_tail_1399_; 
v_tail_1399_ = lean_ctor_get(v_cs_1383_, 1);
if (lean_obj_tag(v_tail_1399_) == 0)
{
lean_object* v_head_1400_; lean_object* v___x_1401_; 
lean_dec(v_n_1382_);
v_head_1400_ = lean_ctor_get(v_cs_1383_, 0);
lean_inc(v_head_1400_);
lean_dec_ref_known(v_cs_1383_, 2);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_head_1400_);
return v___x_1401_;
}
else
{
goto v___jp_1387_;
}
}
else
{
goto v___jp_1387_;
}
v___jp_1387_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1388_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1389_ = l_Lean_MessageData_ofName(v_n_1382_);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_box(0);
v___x_1394_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1383_, v___x_1393_);
v___x_1395_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1394_, v___x_1393_);
v___x_1396_ = l_Lean_MessageData_ofList(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1392_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1397_, v___y_1384_, v___y_1385_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1402_, lean_object* v_cs_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1402_, v_cs_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; 
lean_inc(v_n_1408_);
v___x_1412_ = l_Lean_realizeGlobalConstCore(v_n_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1408_, v_a_1413_, v_a_1409_, v_a_1410_);
return v___x_1414_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_n_1408_);
v_a_1415_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1412_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1412_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_array_to_list(v_a_1429_);
return v___x_1430_;
}
else
{
lean_object* v_head_1431_; 
v_head_1431_ = lean_ctor_get(v_a_1428_, 0);
if (lean_obj_tag(v_head_1431_) == 1)
{
lean_object* v_fields_1432_; 
v_fields_1432_ = lean_ctor_get(v_head_1431_, 1);
if (lean_obj_tag(v_fields_1432_) == 0)
{
lean_object* v_tail_1433_; lean_object* v_n_1434_; lean_object* v___x_1435_; 
lean_inc_ref(v_head_1431_);
v_tail_1433_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_tail_1433_);
lean_dec_ref_known(v_a_1428_, 2);
v_n_1434_ = lean_ctor_get(v_head_1431_, 0);
lean_inc(v_n_1434_);
lean_dec_ref_known(v_head_1431_, 2);
v___x_1435_ = lean_array_push(v_a_1429_, v_n_1434_);
v_a_1428_ = v_tail_1433_;
v_a_1429_ = v___x_1435_;
goto _start;
}
else
{
lean_object* v_tail_1437_; 
v_tail_1437_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_tail_1437_);
lean_dec_ref_known(v_a_1428_, 2);
v_a_1428_ = v_tail_1437_;
goto _start;
}
}
else
{
lean_object* v_tail_1439_; 
v_tail_1439_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_tail_1439_);
lean_dec_ref_known(v_a_1428_, 2);
v_a_1428_ = v_tail_1439_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1447_ = l_Lean_MessageData_ofFormat(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1448_, lean_object* v_k_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
if (lean_obj_tag(v_stx_1448_) == 3)
{
lean_object* v_val_1453_; lean_object* v_preresolved_1454_; lean_object* v___x_1455_; lean_object* v_pre_1456_; uint8_t v___x_1457_; 
v_val_1453_ = lean_ctor_get(v_stx_1448_, 2);
lean_inc(v_val_1453_);
v_preresolved_1454_ = lean_ctor_get(v_stx_1448_, 3);
v___x_1455_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1454_);
v_pre_1456_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1454_, v___x_1455_);
v___x_1457_ = l_List_isEmpty___redArg(v_pre_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref_known(v_stx_1448_, 4);
lean_dec(v_val_1453_);
lean_dec_ref(v_k_1449_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_pre_1456_);
return v___x_1458_;
}
else
{
lean_object* v_toCold_1459_; lean_object* v_currRecDepth_1460_; lean_object* v_ref_1461_; uint8_t v_diag_1462_; uint8_t v_suppressElabErrors_1463_; lean_object* v_ref_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_pre_1456_);
v_toCold_1459_ = lean_ctor_get(v___y_1450_, 0);
v_currRecDepth_1460_ = lean_ctor_get(v___y_1450_, 1);
v_ref_1461_ = lean_ctor_get(v___y_1450_, 2);
v_diag_1462_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*3);
v_suppressElabErrors_1463_ = lean_ctor_get_uint8(v___y_1450_, sizeof(void*)*3 + 1);
v_ref_1464_ = l_Lean_replaceRef(v_stx_1448_, v_ref_1461_);
lean_dec_ref_known(v_stx_1448_, 4);
lean_inc(v_currRecDepth_1460_);
lean_inc_ref(v_toCold_1459_);
v___x_1465_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1465_, 0, v_toCold_1459_);
lean_ctor_set(v___x_1465_, 1, v_currRecDepth_1460_);
lean_ctor_set(v___x_1465_, 2, v_ref_1464_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*3, v_diag_1462_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*3 + 1, v_suppressElabErrors_1463_);
lean_inc(v___y_1451_);
v___x_1466_ = lean_apply_4(v_k_1449_, v_val_1453_, v___x_1465_, v___y_1451_, lean_box(0));
return v___x_1466_;
}
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v_k_1449_);
v___x_1467_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1448_, v___x_1467_, v___y_1450_, v___y_1451_);
lean_dec(v_stx_1448_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1469_, lean_object* v_k_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1469_, v_k_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_toCold_1480_; lean_object* v_currRecDepth_1481_; lean_object* v_ref_1482_; uint8_t v_diag_1483_; uint8_t v_suppressElabErrors_1484_; lean_object* v___x_1485_; lean_object* v_ref_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_toCold_1480_ = lean_ctor_get(v_a_1477_, 0);
v_currRecDepth_1481_ = lean_ctor_get(v_a_1477_, 1);
v_ref_1482_ = lean_ctor_get(v_a_1477_, 2);
v_diag_1483_ = lean_ctor_get_uint8(v_a_1477_, sizeof(void*)*3);
v_suppressElabErrors_1484_ = lean_ctor_get_uint8(v_a_1477_, sizeof(void*)*3 + 1);
v___x_1485_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1486_ = l_Lean_replaceRef(v_stx_1476_, v_ref_1482_);
lean_inc(v_currRecDepth_1481_);
lean_inc_ref(v_toCold_1480_);
v___x_1487_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1487_, 0, v_toCold_1480_);
lean_ctor_set(v___x_1487_, 1, v_currRecDepth_1481_);
lean_ctor_set(v___x_1487_, 2, v_ref_1486_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*3, v_diag_1483_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*3 + 1, v_suppressElabErrors_1484_);
v___x_1488_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1476_, v___x_1485_, v___x_1487_, v_a_1478_);
lean_dec_ref_known(v___x_1487_, 3);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_realizeGlobalConst(v_stx_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
return v_res_1493_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_instMonadEIO(lean_box(0));
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_toApplicative_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1534_; 
v___x_1501_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1502_ = l_StateRefT_x27_instMonad___redArg(v___x_1501_);
v_toApplicative_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1502_, 1);
lean_dec(v_unused_1535_);
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1534_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_toApplicative_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1534_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_toFunctor_1507_; lean_object* v_toSeq_1508_; lean_object* v_toSeqLeft_1509_; lean_object* v_toSeqRight_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1532_; 
v_toFunctor_1507_ = lean_ctor_get(v_toApplicative_1503_, 0);
v_toSeq_1508_ = lean_ctor_get(v_toApplicative_1503_, 2);
v_toSeqLeft_1509_ = lean_ctor_get(v_toApplicative_1503_, 3);
v_toSeqRight_1510_ = lean_ctor_get(v_toApplicative_1503_, 4);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_toApplicative_1503_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v_toApplicative_1503_, 1);
lean_dec(v_unused_1533_);
v___x_1512_ = v_toApplicative_1503_;
v_isShared_1513_ = v_isSharedCheck_1532_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_toSeqRight_1510_);
lean_inc(v_toSeqLeft_1509_);
lean_inc(v_toSeq_1508_);
lean_inc(v_toFunctor_1507_);
lean_dec(v_toApplicative_1503_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1532_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___f_1514_; lean_object* v___f_1515_; lean_object* v___f_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; lean_object* v___f_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1523_; 
v___f_1514_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1515_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1507_);
v___f_1516_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1516_, 0, v_toFunctor_1507_);
v___f_1517_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1517_, 0, v_toFunctor_1507_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___f_1516_);
lean_ctor_set(v___x_1518_, 1, v___f_1517_);
v___f_1519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1519_, 0, v_toSeqRight_1510_);
v___f_1520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1520_, 0, v_toSeqLeft_1509_);
v___f_1521_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1521_, 0, v_toSeq_1508_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 4, v___f_1519_);
lean_ctor_set(v___x_1512_, 3, v___f_1520_);
lean_ctor_set(v___x_1512_, 2, v___f_1521_);
lean_ctor_set(v___x_1512_, 1, v___f_1514_);
lean_ctor_set(v___x_1512_, 0, v___x_1518_);
v___x_1523_ = v___x_1512_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___f_1514_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v___f_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___f_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v___f_1519_);
v___x_1523_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___f_1515_);
lean_ctor_set(v___x_1505_, 0, v___x_1523_);
v___x_1525_ = v___x_1505_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___f_1515_);
v___x_1525_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_195__overap_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = l_instInhabitedOfMonad___redArg(v___x_1525_, v___x_1526_);
v___x_195__overap_1528_ = lean_panic_fn_borrowed(v___x_1527_, v_msg_1497_);
lean_dec(v___x_1527_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
v___x_1529_ = lean_apply_3(v___x_195__overap_1528_, v___y_1498_, v___y_1499_, lean_box(0));
return v___x_1529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
if (lean_obj_tag(v_x_1543_) == 0)
{
return v_x_1542_;
}
else
{
lean_object* v_head_1544_; lean_object* v_tail_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_head_1544_ = lean_ctor_get(v_x_1543_, 0);
v_tail_1545_ = lean_ctor_get(v_x_1543_, 1);
v___x_1546_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1547_ = lean_string_append(v_x_1542_, v___x_1546_);
v___x_1548_ = lean_expr_dbg_to_string(v_head_1544_);
v___x_1549_ = lean_string_append(v___x_1547_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v_x_1542_ = v___x_1549_;
v_x_1543_ = v_tail_1545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1551_, v_x_1552_);
lean_dec(v_x_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1558_;
}
else
{
lean_object* v_tail_1559_; 
v_tail_1559_ = lean_ctor_get(v_x_1557_, 1);
if (lean_obj_tag(v_tail_1559_) == 0)
{
lean_object* v_head_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_head_1560_ = lean_ctor_get(v_x_1557_, 0);
v___x_1561_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1562_ = lean_expr_dbg_to_string(v_head_1560_);
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1565_ = lean_string_append(v___x_1563_, v___x_1564_);
return v___x_1565_;
}
else
{
lean_object* v_head_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint32_t v___x_1571_; lean_object* v___x_1572_; 
v_head_1566_ = lean_ctor_get(v_x_1557_, 0);
v___x_1567_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1568_ = lean_expr_dbg_to_string(v_head_1566_);
v___x_1569_ = lean_string_append(v___x_1567_, v___x_1568_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1569_, v_tail_1559_);
v___x_1571_ = 93;
v___x_1572_ = lean_string_push(v___x_1570_, v___x_1571_);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1573_);
lean_dec(v_x_1573_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1579_ = lean_unsigned_to_nat(11u);
v___x_1580_ = lean_unsigned_to_nat(429u);
v___x_1581_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1582_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1583_ = l_mkPanicMessageWithDecl(v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_, v___x_1578_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1586_, lean_object* v_cs_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
if (lean_obj_tag(v_cs_1587_) == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_id_1586_);
v___x_1591_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1592_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1591_, v___y_1588_, v___y_1589_);
return v___x_1592_;
}
else
{
lean_object* v_tail_1593_; 
v_tail_1593_ = lean_ctor_get(v_cs_1587_, 1);
if (lean_obj_tag(v_tail_1593_) == 0)
{
lean_object* v_head_1594_; lean_object* v___x_1595_; 
lean_dec(v_id_1586_);
v_head_1594_ = lean_ctor_get(v_cs_1587_, 0);
lean_inc(v_head_1594_);
lean_dec_ref_known(v_cs_1587_, 2);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_head_1594_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1596_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1597_ = lean_box(0);
v___x_1598_ = 0;
lean_inc(v_id_1586_);
v___x_1599_ = l_Lean_Syntax_formatStx(v_id_1586_, v___x_1597_, v___x_1598_);
v___x_1600_ = l_Std_Format_defWidth;
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = l_Std_Format_pretty(v___x_1599_, v___x_1600_, v___x_1601_, v___x_1601_);
v___x_1603_ = lean_string_append(v___x_1596_, v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1605_ = lean_string_append(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1587_, v___x_1606_);
v___x_1608_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_string_append(v___x_1605_, v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___x_1611_ = l_Lean_MessageData_ofFormat(v___x_1610_);
v___x_1612_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1586_, v___x_1611_, v___y_1588_, v___y_1589_);
lean_dec(v_id_1586_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1613_, lean_object* v_cs_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1613_, v_cs_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; 
lean_inc(v_id_1619_);
v___x_1623_ = l_Lean_realizeGlobalConst(v_id_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1619_, v_a_1624_, v_a_1620_, v_a_1621_);
return v___x_1625_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_id_1619_);
v_a_1626_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1623_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1623_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_realizeGlobalConstNoOverload(v_id_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1638_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(3863082579u);
v___x_1671_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1672_ = l_Lean_Name_num___override(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1675_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1676_ = l_Lean_Name_str___override(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1679_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1680_ = l_Lean_Name_str___override(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(2u);
v___x_1682_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1683_ = l_Lean_Name_num___override(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1686_ = 0;
v___x_1687_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1688_ = l_Lean_registerTraceClass(v___x_1685_, v___x_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1690_;
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

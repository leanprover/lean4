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
lean_object* v___x_145_; lean_object* v_env_146_; lean_object* v_options_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_env_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_146_);
lean_dec(v___x_145_);
v_options_147_ = lean_ctor_get(v___y_142_, 2);
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_147_);
v___x_150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_150_, 0, v_env_146_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set(v___x_150_, 3, v_options_147_);
v___x_151_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_msgData_141_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object* v_msgData_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t v_sz_158_, size_t v_i_159_, lean_object* v_bs_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_161_ == 0)
{
return v_bs_160_;
}
else
{
lean_object* v_v_162_; lean_object* v_msg_163_; lean_object* v___x_164_; lean_object* v_bs_x27_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_v_162_ = lean_array_uget_borrowed(v_bs_160_, v_i_159_);
v_msg_163_ = lean_ctor_get(v_v_162_, 1);
lean_inc_ref(v_msg_163_);
v___x_164_ = lean_unsigned_to_nat(0u);
v_bs_x27_165_ = lean_array_uset(v_bs_160_, v_i_159_, v___x_164_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_159_, v___x_166_);
v___x_168_ = lean_array_uset(v_bs_x27_165_, v_i_159_, v_msg_163_);
v_i_159_ = v___x_167_;
v_bs_160_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_170_, lean_object* v_i_171_, lean_object* v_bs_172_){
_start:
{
size_t v_sz_boxed_173_; size_t v_i_boxed_174_; lean_object* v_res_175_; 
v_sz_boxed_173_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_174_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_boxed_173_, v_i_boxed_174_, v_bs_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_oldTraces_176_, lean_object* v_data_177_, lean_object* v_ref_178_, lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_fileName_183_; lean_object* v_fileMap_184_; lean_object* v_options_185_; lean_object* v_currRecDepth_186_; lean_object* v_maxRecDepth_187_; lean_object* v_ref_188_; lean_object* v_currNamespace_189_; lean_object* v_openDecls_190_; lean_object* v_initHeartbeats_191_; lean_object* v_maxHeartbeats_192_; lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; uint8_t v_diag_195_; lean_object* v_cancelTk_x3f_196_; uint8_t v_suppressElabErrors_197_; lean_object* v_inheritedTraceOptions_198_; lean_object* v___x_199_; lean_object* v_traceState_200_; lean_object* v_traces_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v_msg_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_247_; 
v_fileName_183_ = lean_ctor_get(v___y_180_, 0);
v_fileMap_184_ = lean_ctor_get(v___y_180_, 1);
v_options_185_ = lean_ctor_get(v___y_180_, 2);
v_currRecDepth_186_ = lean_ctor_get(v___y_180_, 3);
v_maxRecDepth_187_ = lean_ctor_get(v___y_180_, 4);
v_ref_188_ = lean_ctor_get(v___y_180_, 5);
v_currNamespace_189_ = lean_ctor_get(v___y_180_, 6);
v_openDecls_190_ = lean_ctor_get(v___y_180_, 7);
v_initHeartbeats_191_ = lean_ctor_get(v___y_180_, 8);
v_maxHeartbeats_192_ = lean_ctor_get(v___y_180_, 9);
v_quotContext_193_ = lean_ctor_get(v___y_180_, 10);
v_currMacroScope_194_ = lean_ctor_get(v___y_180_, 11);
v_diag_195_ = lean_ctor_get_uint8(v___y_180_, sizeof(void*)*14);
v_cancelTk_x3f_196_ = lean_ctor_get(v___y_180_, 12);
v_suppressElabErrors_197_ = lean_ctor_get_uint8(v___y_180_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_198_ = lean_ctor_get(v___y_180_, 13);
v___x_199_ = lean_st_ref_get(v___y_181_);
v_traceState_200_ = lean_ctor_get(v___x_199_, 4);
lean_inc_ref(v_traceState_200_);
lean_dec(v___x_199_);
v_traces_201_ = lean_ctor_get(v_traceState_200_, 0);
lean_inc_ref(v_traces_201_);
lean_dec_ref(v_traceState_200_);
v_ref_202_ = l_Lean_replaceRef(v_ref_178_, v_ref_188_);
lean_inc_ref(v_inheritedTraceOptions_198_);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_currMacroScope_194_);
lean_inc(v_quotContext_193_);
lean_inc(v_maxHeartbeats_192_);
lean_inc(v_initHeartbeats_191_);
lean_inc(v_openDecls_190_);
lean_inc(v_currNamespace_189_);
lean_inc(v_maxRecDepth_187_);
lean_inc(v_currRecDepth_186_);
lean_inc_ref(v_options_185_);
lean_inc_ref(v_fileMap_184_);
lean_inc_ref(v_fileName_183_);
v___x_203_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_203_, 0, v_fileName_183_);
lean_ctor_set(v___x_203_, 1, v_fileMap_184_);
lean_ctor_set(v___x_203_, 2, v_options_185_);
lean_ctor_set(v___x_203_, 3, v_currRecDepth_186_);
lean_ctor_set(v___x_203_, 4, v_maxRecDepth_187_);
lean_ctor_set(v___x_203_, 5, v_ref_202_);
lean_ctor_set(v___x_203_, 6, v_currNamespace_189_);
lean_ctor_set(v___x_203_, 7, v_openDecls_190_);
lean_ctor_set(v___x_203_, 8, v_initHeartbeats_191_);
lean_ctor_set(v___x_203_, 9, v_maxHeartbeats_192_);
lean_ctor_set(v___x_203_, 10, v_quotContext_193_);
lean_ctor_set(v___x_203_, 11, v_currMacroScope_194_);
lean_ctor_set(v___x_203_, 12, v_cancelTk_x3f_196_);
lean_ctor_set(v___x_203_, 13, v_inheritedTraceOptions_198_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*14, v_diag_195_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*14 + 1, v_suppressElabErrors_197_);
v___x_204_ = l_Lean_PersistentArray_toArray___redArg(v_traces_201_);
lean_dec_ref(v_traces_201_);
v_sz_205_ = lean_array_size(v___x_204_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_205_, v___x_206_, v___x_204_);
v_msg_208_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_208_, 0, v_data_177_);
lean_ctor_set(v_msg_208_, 1, v_msg_179_);
lean_ctor_set(v_msg_208_, 2, v___x_207_);
v___x_209_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_208_, v___x_203_, v___y_181_);
lean_dec_ref_known(v___x_203_, 14);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_247_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_247_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_247_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_traceState_215_; lean_object* v_env_216_; lean_object* v_nextMacroScope_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_cache_220_; lean_object* v_messages_221_; lean_object* v_infoState_222_; lean_object* v_snapshotTasks_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v___x_214_ = lean_st_ref_take(v___y_181_);
v_traceState_215_ = lean_ctor_get(v___x_214_, 4);
v_env_216_ = lean_ctor_get(v___x_214_, 0);
v_nextMacroScope_217_ = lean_ctor_get(v___x_214_, 1);
v_ngen_218_ = lean_ctor_get(v___x_214_, 2);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_214_, 3);
v_cache_220_ = lean_ctor_get(v___x_214_, 5);
v_messages_221_ = lean_ctor_get(v___x_214_, 6);
v_infoState_222_ = lean_ctor_get(v___x_214_, 7);
v_snapshotTasks_223_ = lean_ctor_get(v___x_214_, 8);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_246_ == 0)
{
v___x_225_ = v___x_214_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snapshotTasks_223_);
lean_inc(v_infoState_222_);
lean_inc(v_messages_221_);
lean_inc(v_cache_220_);
lean_inc(v_traceState_215_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_env_216_);
lean_dec(v___x_214_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint64_t v_tid_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_244_; 
v_tid_227_ = lean_ctor_get_uint64(v_traceState_215_, sizeof(void*)*1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_traceState_215_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_traceState_215_, 0);
lean_dec(v_unused_245_);
v___x_229_ = v_traceState_215_;
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_traceState_215_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_ref_178_);
lean_ctor_set(v___x_231_, 1, v_a_210_);
v___x_232_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_176_, v___x_231_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_232_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_232_);
lean_ctor_set_uint64(v_reuseFailAlloc_243_, sizeof(void*)*1, v_tid_227_);
v___x_234_ = v_reuseFailAlloc_243_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 4, v___x_234_);
v___x_236_ = v___x_225_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_env_216_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_messages_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_snapshotTasks_223_);
v___x_236_ = v_reuseFailAlloc_242_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = lean_st_ref_put(v___y_181_, v___x_236_);
v___x_238_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_238_);
v___x_240_ = v___x_212_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_248_, lean_object* v_data_249_, lean_object* v_ref_250_, lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_248_, v_data_249_, v_ref_250_, v_msg_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_a_258_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v_x_256_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v_x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v_x_256_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v_x_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_274_);
return v_res_276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_277_){
_start:
{
if (lean_obj_tag(v_e_277_) == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 2;
return v___x_278_;
}
else
{
lean_object* v_a_279_; uint8_t v___x_280_; 
v_a_279_ = lean_ctor_get(v_e_277_, 0);
v___x_280_ = lean_unbox(v_a_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = 1;
return v___x_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_283_);
lean_dec_ref(v_e_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_286_; double v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_float_of_nat(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_291_; double v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1000u);
v___x_292_ = lean_float_of_nat(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_293_, uint8_t v_collapsed_294_, lean_object* v_tag_295_, lean_object* v_opts_296_, uint8_t v_clsEnabled_297_, lean_object* v_oldTraces_298_, lean_object* v_msg_299_, lean_object* v_resStartStop_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v_data_309_; lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___y_325_; lean_object* v_a_326_; uint8_t v___y_341_; double v___y_372_; 
v_fst_304_ = lean_ctor_get(v_resStartStop_300_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v_resStartStop_300_, 1);
lean_inc(v_snd_305_);
lean_dec_ref(v_resStartStop_300_);
v_fst_320_ = lean_ctor_get(v_snd_305_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_snd_305_, 1);
lean_inc(v_snd_321_);
lean_dec(v_snd_305_);
v___x_322_ = l_Lean_trace_profiler;
v___x_323_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_296_, v___x_322_);
if (v___x_323_ == 0)
{
v___y_341_ = v___x_323_;
goto v___jp_340_;
}
else
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = l_Lean_trace_profiler_useHeartbeats;
v___x_378_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_296_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; double v___x_381_; double v___x_382_; double v___x_383_; 
v___x_379_ = l_Lean_trace_profiler_threshold;
v___x_380_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_296_, v___x_379_);
v___x_381_ = lean_float_of_nat(v___x_380_);
v___x_382_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_383_ = lean_float_div(v___x_381_, v___x_382_);
v___y_372_ = v___x_383_;
goto v___jp_371_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; double v___x_386_; 
v___x_384_ = l_Lean_trace_profiler_threshold;
v___x_385_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_296_, v___x_384_);
v___x_386_ = lean_float_of_nat(v___x_385_);
v___y_372_ = v___x_386_;
goto v___jp_371_;
}
}
v___jp_306_:
{
lean_object* v___x_310_; 
lean_inc(v___y_308_);
v___x_310_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_298_, v_data_309_, v___y_308_, v___y_307_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_311_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_304_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_fst_304_);
v_a_312_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
v___jp_324_:
{
uint8_t v_result_327_; lean_object* v___x_328_; lean_object* v___x_329_; double v___x_330_; lean_object* v_data_331_; 
v_result_327_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_304_);
v___x_328_ = lean_box(v_result_327_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
lean_inc_ref(v_tag_295_);
lean_inc_ref(v___x_329_);
lean_inc(v_cls_293_);
v_data_331_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_331_, 0, v_cls_293_);
lean_ctor_set(v_data_331_, 1, v___x_329_);
lean_ctor_set(v_data_331_, 2, v_tag_295_);
lean_ctor_set_float(v_data_331_, sizeof(void*)*3, v___x_330_);
lean_ctor_set_float(v_data_331_, sizeof(void*)*3 + 8, v___x_330_);
lean_ctor_set_uint8(v_data_331_, sizeof(void*)*3 + 16, v_collapsed_294_);
if (v___x_323_ == 0)
{
lean_dec_ref_known(v___x_329_, 1);
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
lean_dec_ref(v_tag_295_);
lean_dec(v_cls_293_);
v___y_307_ = v_a_326_;
v___y_308_ = v___y_325_;
v_data_309_ = v_data_331_;
goto v___jp_306_;
}
else
{
lean_object* v_data_332_; double v___x_333_; double v___x_334_; 
lean_dec_ref_known(v_data_331_, 3);
v_data_332_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_332_, 0, v_cls_293_);
lean_ctor_set(v_data_332_, 1, v___x_329_);
lean_ctor_set(v_data_332_, 2, v_tag_295_);
v___x_333_ = lean_unbox_float(v_fst_320_);
lean_dec(v_fst_320_);
lean_ctor_set_float(v_data_332_, sizeof(void*)*3, v___x_333_);
v___x_334_ = lean_unbox_float(v_snd_321_);
lean_dec(v_snd_321_);
lean_ctor_set_float(v_data_332_, sizeof(void*)*3 + 8, v___x_334_);
lean_ctor_set_uint8(v_data_332_, sizeof(void*)*3 + 16, v_collapsed_294_);
v___y_307_ = v_a_326_;
v___y_308_ = v___y_325_;
v_data_309_ = v_data_332_;
goto v___jp_306_;
}
}
v___jp_335_:
{
lean_object* v_ref_336_; lean_object* v___x_337_; 
v_ref_336_ = lean_ctor_get(v___y_301_, 5);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v_fst_304_);
v___x_337_ = lean_apply_4(v_msg_299_, v_fst_304_, v___y_301_, v___y_302_, lean_box(0));
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___y_325_ = v_ref_336_;
v_a_326_ = v_a_338_;
goto v___jp_324_;
}
else
{
lean_object* v___x_339_; 
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
v___y_325_ = v_ref_336_;
v_a_326_ = v___x_339_;
goto v___jp_324_;
}
}
v___jp_340_:
{
if (v_clsEnabled_297_ == 0)
{
if (v___y_341_ == 0)
{
lean_object* v___x_342_; lean_object* v_traceState_343_; lean_object* v_env_344_; lean_object* v_nextMacroScope_345_; lean_object* v_ngen_346_; lean_object* v_auxDeclNGen_347_; lean_object* v_cache_348_; lean_object* v_messages_349_; lean_object* v_infoState_350_; lean_object* v_snapshotTasks_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_snd_321_);
lean_dec(v_fst_320_);
lean_dec_ref(v_msg_299_);
lean_dec_ref(v_tag_295_);
lean_dec(v_cls_293_);
v___x_342_ = lean_st_ref_take(v___y_302_);
v_traceState_343_ = lean_ctor_get(v___x_342_, 4);
v_env_344_ = lean_ctor_get(v___x_342_, 0);
v_nextMacroScope_345_ = lean_ctor_get(v___x_342_, 1);
v_ngen_346_ = lean_ctor_get(v___x_342_, 2);
v_auxDeclNGen_347_ = lean_ctor_get(v___x_342_, 3);
v_cache_348_ = lean_ctor_get(v___x_342_, 5);
v_messages_349_ = lean_ctor_get(v___x_342_, 6);
v_infoState_350_ = lean_ctor_get(v___x_342_, 7);
v_snapshotTasks_351_ = lean_ctor_get(v___x_342_, 8);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_370_ == 0)
{
v___x_353_ = v___x_342_;
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snapshotTasks_351_);
lean_inc(v_infoState_350_);
lean_inc(v_messages_349_);
lean_inc(v_cache_348_);
lean_inc(v_traceState_343_);
lean_inc(v_auxDeclNGen_347_);
lean_inc(v_ngen_346_);
lean_inc(v_nextMacroScope_345_);
lean_inc(v_env_344_);
lean_dec(v___x_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint64_t v_tid_355_; lean_object* v_traces_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_369_; 
v_tid_355_ = lean_ctor_get_uint64(v_traceState_343_, sizeof(void*)*1);
v_traces_356_ = lean_ctor_get(v_traceState_343_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_traceState_343_);
if (v_isSharedCheck_369_ == 0)
{
v___x_358_ = v_traceState_343_;
v_isShared_359_ = v_isSharedCheck_369_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_traces_356_);
lean_dec(v_traceState_343_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_369_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_298_, v_traces_356_);
lean_dec_ref(v_traces_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_360_);
lean_ctor_set_uint64(v_reuseFailAlloc_368_, sizeof(void*)*1, v_tid_355_);
v___x_362_ = v_reuseFailAlloc_368_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v___x_362_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_env_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_nextMacroScope_345_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_ngen_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_auxDeclNGen_347_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v_cache_348_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_messages_349_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v_infoState_350_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v_snapshotTasks_351_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_st_ref_put(v___y_302_, v___x_364_);
v___x_366_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_304_);
return v___x_366_;
}
}
}
}
}
else
{
goto v___jp_335_;
}
}
else
{
goto v___jp_335_;
}
}
v___jp_371_:
{
double v___x_373_; double v___x_374_; double v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_unbox_float(v_snd_321_);
v___x_374_ = lean_unbox_float(v_fst_320_);
v___x_375_ = lean_float_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_float_decLt(v___y_372_, v___x_375_);
v___y_341_ = v___x_376_;
goto v___jp_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_387_, lean_object* v_collapsed_388_, lean_object* v_tag_389_, lean_object* v_opts_390_, lean_object* v_clsEnabled_391_, lean_object* v_oldTraces_392_, lean_object* v_msg_393_, lean_object* v_resStartStop_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
uint8_t v_collapsed_boxed_398_; uint8_t v_clsEnabled_boxed_399_; lean_object* v_res_400_; 
v_collapsed_boxed_398_ = lean_unbox(v_collapsed_388_);
v_clsEnabled_boxed_399_ = lean_unbox(v_clsEnabled_391_);
v_res_400_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_387_, v_collapsed_boxed_398_, v_tag_389_, v_opts_390_, v_clsEnabled_boxed_399_, v_oldTraces_392_, v_msg_393_, v_resStartStop_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v_opts_390_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_408_ == 0)
{
lean_object* v___x_5228__overap_409_; lean_object* v___x_410_; 
v___x_5228__overap_409_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
lean_inc(v___x_5228__overap_409_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
lean_inc(v_name_401_);
v___x_410_ = lean_apply_4(v___x_5228__overap_409_, v_name_401_, v___y_405_, v___y_406_, lean_box(0));
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_422_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_422_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
uint8_t v___x_415_; 
v___x_415_ = lean_unbox(v_a_411_);
if (v___x_415_ == 0)
{
size_t v___x_416_; size_t v___x_417_; 
lean_del_object(v___x_413_);
lean_dec(v_a_411_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_403_, v___x_416_);
v_i_403_ = v___x_417_;
goto _start;
}
else
{
lean_object* v___x_420_; 
lean_dec(v_name_401_);
if (v_isShared_414_ == 0)
{
v___x_420_ = v___x_413_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_411_);
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
lean_dec(v_name_401_);
return v___x_410_;
}
}
else
{
uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_name_401_);
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
lean_object* v_options_452_; lean_object* v_inheritedTraceOptions_453_; uint8_t v_hasTrace_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___y_458_; 
v_options_452_ = lean_ctor_get(v_a_449_, 2);
v_inheritedTraceOptions_453_ = lean_ctor_get(v_a_449_, 13);
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
lean_dec(v_name_448_);
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
lean_dec(v_name_448_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_456_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_477_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_475_, v___x_481_, v___x_482_, v_a_449_, v_a_450_);
lean_dec(v___x_475_);
v___y_458_ = v___x_483_;
goto v___jp_457_;
}
}
}
else
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v_a_492_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v_a_507_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v_a_513_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v_a_525_; 
lean_inc(v_name_448_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_484_, 0, v_name_448_);
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
lean_dec(v_name_448_);
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
lean_dec(v_name_448_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_456_);
return v___x_576_;
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_573_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_571_, v___x_577_, v___x_578_, v_a_449_, v_a_450_);
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
v___x_503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_485_, v_hasTrace_454_, v___x_486_, v_options_452_, v___x_488_, v___y_490_, v___f_484_, v___x_502_, v_a_449_, v_a_450_);
v___y_458_ = v___x_503_;
goto v___jp_457_;
}
v___jp_504_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_box(v_a_507_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
v___y_490_ = v___y_506_;
v___y_491_ = v___y_505_;
v_a_492_ = v___x_509_;
goto v___jp_489_;
}
v___jp_510_:
{
lean_object* v___x_514_; double v___x_515_; double v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_514_ = lean_io_get_num_heartbeats();
v___x_515_ = lean_float_of_nat(v___y_511_);
v___x_516_ = lean_float_of_nat(v___x_514_);
v___x_517_ = lean_box_float(v___x_515_);
v___x_518_ = lean_box_float(v___x_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_513_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_485_, v_hasTrace_454_, v___x_486_, v_options_452_, v___x_488_, v___y_512_, v___f_484_, v___x_520_, v_a_449_, v_a_450_);
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
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_450_);
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
lean_dec(v_name_448_);
v___y_505_ = v___x_533_;
v___y_506_ = v_a_530_;
v_a_507_ = v___x_537_;
goto v___jp_504_;
}
else
{
if (v___x_537_ == 0)
{
lean_dec(v___x_534_);
lean_dec(v_name_448_);
v___y_505_ = v___x_533_;
v___y_506_ = v_a_530_;
v_a_507_ = v___x_537_;
goto v___jp_504_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_534_, v___x_538_, v___x_539_, v_a_449_, v_a_450_);
lean_dec(v___x_534_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint8_t v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = lean_unbox(v_a_541_);
lean_dec(v_a_541_);
v___y_505_ = v___x_533_;
v___y_506_ = v_a_530_;
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
lean_dec(v_name_448_);
v___y_523_ = v___x_551_;
v___y_524_ = v_a_530_;
v_a_525_ = v___x_555_;
goto v___jp_522_;
}
else
{
if (v___x_555_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_name_448_);
v___y_523_ = v___x_551_;
v___y_524_ = v_a_530_;
v_a_525_ = v___x_555_;
goto v___jp_522_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_448_, v___x_552_, v___x_556_, v___x_557_, v_a_449_, v_a_450_);
lean_dec(v___x_552_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_unbox(v_a_559_);
lean_dec(v_a_559_);
v___y_523_ = v___x_551_;
v___y_524_ = v_a_530_;
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
v___y_511_ = v___x_551_;
v___y_512_ = v_a_530_;
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
uint8_t v_suppressElabErrors_boxed_635_; uint8_t v___y_4741__boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_suppressElabErrors_boxed_635_ = lean_unbox(v_suppressElabErrors_632_);
v___y_4741__boxed_636_ = lean_unbox(v___y_633_);
v_res_637_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_635_, v___y_4741__boxed_636_, v_x_634_);
lean_dec(v_x_634_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_639_, lean_object* v_msgData_640_, uint8_t v_severity_641_, uint8_t v_isSilent_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; uint8_t v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; uint8_t v___y_712_; uint8_t v___y_713_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; uint8_t v___x_730_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; uint8_t v___y_738_; uint8_t v___y_740_; uint8_t v___x_755_; 
v___x_730_ = 2;
v___x_755_ = l_Lean_instBEqMessageSeverity_beq(v_severity_641_, v___x_730_);
if (v___x_755_ == 0)
{
v___y_740_ = v___x_755_;
goto v___jp_739_;
}
else
{
uint8_t v___x_756_; 
lean_inc_ref(v_msgData_640_);
v___x_756_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_640_);
v___y_740_ = v___x_756_;
goto v___jp_739_;
}
v___jp_646_:
{
lean_object* v___x_656_; lean_object* v_currNamespace_657_; lean_object* v_openDecls_658_; lean_object* v_env_659_; lean_object* v_nextMacroScope_660_; lean_object* v_ngen_661_; lean_object* v_auxDeclNGen_662_; lean_object* v_traceState_663_; lean_object* v_cache_664_; lean_object* v_messages_665_; lean_object* v_infoState_666_; lean_object* v_snapshotTasks_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_681_; 
v___x_656_ = lean_st_ref_take(v___y_655_);
v_currNamespace_657_ = lean_ctor_get(v___y_654_, 6);
v_openDecls_658_ = lean_ctor_get(v___y_654_, 7);
v_env_659_ = lean_ctor_get(v___x_656_, 0);
v_nextMacroScope_660_ = lean_ctor_get(v___x_656_, 1);
v_ngen_661_ = lean_ctor_get(v___x_656_, 2);
v_auxDeclNGen_662_ = lean_ctor_get(v___x_656_, 3);
v_traceState_663_ = lean_ctor_get(v___x_656_, 4);
v_cache_664_ = lean_ctor_get(v___x_656_, 5);
v_messages_665_ = lean_ctor_get(v___x_656_, 6);
v_infoState_666_ = lean_ctor_get(v___x_656_, 7);
v_snapshotTasks_667_ = lean_ctor_get(v___x_656_, 8);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_681_ == 0)
{
v___x_669_ = v___x_656_;
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snapshotTasks_667_);
lean_inc(v_infoState_666_);
lean_inc(v_messages_665_);
lean_inc(v_cache_664_);
lean_inc(v_traceState_663_);
lean_inc(v_auxDeclNGen_662_);
lean_inc(v_ngen_661_);
lean_inc(v_nextMacroScope_660_);
lean_inc(v_env_659_);
lean_dec(v___x_656_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_inc(v_openDecls_658_);
lean_inc(v_currNamespace_657_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_currNamespace_657_);
lean_ctor_set(v___x_671_, 1, v_openDecls_658_);
v___x_672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___y_652_);
lean_inc_ref(v___y_653_);
lean_inc_ref(v___y_647_);
v___x_673_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_673_, 0, v___y_647_);
lean_ctor_set(v___x_673_, 1, v___y_649_);
lean_ctor_set(v___x_673_, 2, v___y_648_);
lean_ctor_set(v___x_673_, 3, v___y_653_);
lean_ctor_set(v___x_673_, 4, v___x_672_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*5, v___y_651_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*5 + 1, v___y_650_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*5 + 2, v_isSilent_642_);
v___x_674_ = l_Lean_MessageLog_add(v___x_673_, v_messages_665_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 6, v___x_674_);
v___x_676_ = v___x_669_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_env_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_nextMacroScope_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_ngen_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_auxDeclNGen_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_traceState_663_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v_cache_664_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_infoState_666_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_snapshotTasks_667_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_st_ref_put(v___y_655_, v___x_676_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
v___jp_682_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_706_; 
v___x_691_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_640_);
v___x_692_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_691_, v___y_643_, v___y_644_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_706_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_inc_ref_n(v___y_685_, 2);
v___x_697_ = l_Lean_FileMap_toPosition(v___y_685_, v___y_689_);
lean_dec(v___y_689_);
v___x_698_ = l_Lean_FileMap_toPosition(v___y_685_, v___y_690_);
lean_dec(v___y_690_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_686_ == 0)
{
lean_del_object(v___x_695_);
lean_dec_ref(v___y_683_);
v___y_647_ = v___y_684_;
v___y_648_ = v___x_699_;
v___y_649_ = v___x_697_;
v___y_650_ = v___y_688_;
v___y_651_ = v___y_687_;
v___y_652_ = v_a_693_;
v___y_653_ = v___x_700_;
v___y_654_ = v___y_643_;
v___y_655_ = v___y_644_;
goto v___jp_646_;
}
else
{
uint8_t v___x_701_; 
lean_inc(v_a_693_);
v___x_701_ = l_Lean_MessageData_hasTag(v___y_683_, v_a_693_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec_ref_known(v___x_699_, 1);
lean_dec_ref(v___x_697_);
lean_dec(v_a_693_);
v___x_702_ = lean_box(0);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_702_);
v___x_704_ = v___x_695_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_del_object(v___x_695_);
v___y_647_ = v___y_684_;
v___y_648_ = v___x_699_;
v___y_649_ = v___x_697_;
v___y_650_ = v___y_688_;
v___y_651_ = v___y_687_;
v___y_652_ = v_a_693_;
v___y_653_ = v___x_700_;
v___y_654_ = v___y_643_;
v___y_655_ = v___y_644_;
goto v___jp_646_;
}
}
}
}
v___jp_707_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Syntax_getTailPos_x3f(v___y_709_, v___y_713_);
lean_dec(v___y_709_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_inc(v___y_715_);
v___y_683_ = v___y_708_;
v___y_684_ = v___y_711_;
v___y_685_ = v___y_710_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_713_;
v___y_688_ = v___y_712_;
v___y_689_ = v___y_715_;
v___y_690_ = v___y_715_;
goto v___jp_682_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v___x_716_, 1);
v___y_683_ = v___y_708_;
v___y_684_ = v___y_711_;
v___y_685_ = v___y_710_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_713_;
v___y_688_ = v___y_712_;
v___y_689_ = v___y_715_;
v___y_690_ = v_val_717_;
goto v___jp_682_;
}
}
v___jp_718_:
{
lean_object* v_ref_726_; lean_object* v___x_727_; 
v_ref_726_ = l_Lean_replaceRef(v_ref_639_, v___y_724_);
v___x_727_ = l_Lean_Syntax_getPos_x3f(v_ref_726_, v___y_723_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___y_708_ = v___y_719_;
v___y_709_ = v_ref_726_;
v___y_710_ = v___y_721_;
v___y_711_ = v___y_720_;
v___y_712_ = v___y_725_;
v___y_713_ = v___y_723_;
v___y_714_ = v___y_722_;
v___y_715_ = v___x_728_;
goto v___jp_707_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_727_, 1);
v___y_708_ = v___y_719_;
v___y_709_ = v_ref_726_;
v___y_710_ = v___y_721_;
v___y_711_ = v___y_720_;
v___y_712_ = v___y_725_;
v___y_713_ = v___y_723_;
v___y_714_ = v___y_722_;
v___y_715_ = v_val_729_;
goto v___jp_707_;
}
}
v___jp_731_:
{
if (v___y_738_ == 0)
{
v___y_719_ = v___y_736_;
v___y_720_ = v___y_733_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_737_;
v___y_724_ = v___y_735_;
v___y_725_ = v_severity_641_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___y_736_;
v___y_720_ = v___y_733_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_737_;
v___y_724_ = v___y_735_;
v___y_725_ = v___x_730_;
goto v___jp_718_;
}
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
lean_object* v_fileName_741_; lean_object* v_fileMap_742_; lean_object* v_options_743_; lean_object* v_ref_744_; uint8_t v_suppressElabErrors_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___f_748_; uint8_t v___x_749_; uint8_t v___x_750_; 
v_fileName_741_ = lean_ctor_get(v___y_643_, 0);
v_fileMap_742_ = lean_ctor_get(v___y_643_, 1);
v_options_743_ = lean_ctor_get(v___y_643_, 2);
v_ref_744_ = lean_ctor_get(v___y_643_, 5);
v_suppressElabErrors_745_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*14 + 1);
v___x_746_ = lean_box(v_suppressElabErrors_745_);
v___x_747_ = lean_box(v___y_740_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_748_, 0, v___x_746_);
lean_closure_set(v___f_748_, 1, v___x_747_);
v___x_749_ = 1;
v___x_750_ = l_Lean_instBEqMessageSeverity_beq(v_severity_641_, v___x_749_);
if (v___x_750_ == 0)
{
v___y_732_ = v_fileMap_742_;
v___y_733_ = v_fileName_741_;
v___y_734_ = v_suppressElabErrors_745_;
v___y_735_ = v_ref_744_;
v___y_736_ = v___f_748_;
v___y_737_ = v___y_740_;
v___y_738_ = v___x_750_;
goto v___jp_731_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = l_Lean_warningAsError;
v___x_752_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_743_, v___x_751_);
v___y_732_ = v_fileMap_742_;
v___y_733_ = v_fileName_741_;
v___y_734_ = v_suppressElabErrors_745_;
v___y_735_ = v_ref_744_;
v___y_736_ = v___f_748_;
v___y_737_ = v___y_740_;
v___y_738_ = v___x_752_;
goto v___jp_731_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_msgData_640_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_757_, lean_object* v_msgData_758_, lean_object* v_severity_759_, lean_object* v_isSilent_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_severity_boxed_764_; uint8_t v_isSilent_boxed_765_; lean_object* v_res_766_; 
v_severity_boxed_764_ = lean_unbox(v_severity_759_);
v_isSilent_boxed_765_ = lean_unbox(v_isSilent_760_);
v_res_766_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_757_, v_msgData_758_, v_severity_boxed_764_, v_isSilent_boxed_765_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v_ref_757_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_767_, uint8_t v_severity_768_, uint8_t v_isSilent_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_ref_773_; lean_object* v___x_774_; 
v_ref_773_ = lean_ctor_get(v___y_770_, 5);
v___x_774_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_773_, v_msgData_767_, v_severity_768_, v_isSilent_769_, v___y_770_, v___y_771_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_775_, lean_object* v_severity_776_, lean_object* v_isSilent_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
uint8_t v_severity_boxed_781_; uint8_t v_isSilent_boxed_782_; lean_object* v_res_783_; 
v_severity_boxed_781_ = lean_unbox(v_severity_776_);
v_isSilent_boxed_782_ = lean_unbox(v_isSilent_777_);
v_res_783_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_775_, v_severity_boxed_781_, v_isSilent_boxed_782_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = 2;
v___x_789_ = 0;
v___x_790_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_784_, v___x_788_, v___x_789_, v___y_785_, v___y_786_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_795_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v___x_808_; 
lean_dec(v_id_802_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_x_804_);
return v___x_808_;
}
else
{
lean_object* v_head_809_; lean_object* v_tail_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_860_; 
v_head_809_ = lean_ctor_get(v_x_803_, 0);
v_tail_810_ = lean_ctor_get(v_x_803_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_860_ == 0)
{
v___x_812_ = v_x_803_;
v_isShared_813_ = v_isSharedCheck_860_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_tail_810_);
lean_inc(v_head_809_);
lean_dec(v_x_803_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_860_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
uint8_t v_a_820_; lean_object* v_fst_822_; lean_object* v___x_823_; lean_object* v_env_824_; uint8_t v___x_825_; uint8_t v___x_826_; 
v_fst_822_ = lean_ctor_get(v_head_809_, 0);
v___x_823_ = lean_st_ref_get(v___y_806_);
v_env_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_env_824_);
lean_dec(v___x_823_);
v___x_825_ = 1;
lean_inc(v_fst_822_);
v___x_826_ = l_Lean_Environment_contains(v_env_824_, v_fst_822_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_inc(v_fst_822_);
v___x_827_ = l_Lean_executeReservedNameAction(v_fst_822_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; lean_object* v_env_829_; uint8_t v___x_830_; 
lean_dec_ref_known(v___x_827_, 1);
v___x_828_ = lean_st_ref_get(v___y_806_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = l_Lean_Environment_containsOnBranch(v_env_829_, v_fst_822_);
lean_dec_ref(v_env_829_);
v_a_820_ = v___x_830_;
goto v___jp_819_;
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_859_; 
v_a_831_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_859_ == 0)
{
v___x_833_ = v___x_827_;
v_isShared_834_ = v_isSharedCheck_859_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_859_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___y_836_; uint8_t v___x_857_; 
v___x_857_ = l_Lean_Exception_isInterrupt(v_a_831_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; 
lean_inc(v_a_831_);
v___x_858_ = l_Lean_Exception_isRuntime(v_a_831_);
v___y_836_ = v___x_858_;
goto v___jp_835_;
}
else
{
v___y_836_ = v___x_857_;
goto v___jp_835_;
}
v___jp_835_:
{
if (v___y_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_833_);
v___x_837_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_802_);
v___x_838_ = l_Lean_MessageData_ofName(v_id_802_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_Exception_toMessageData(v_a_831_);
v___x_843_ = l_Lean_indentD(v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_841_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_844_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_dec_ref_known(v___x_845_, 1);
v_a_820_ = v___x_826_;
goto v___jp_819_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_del_object(v___x_812_);
lean_dec(v_tail_810_);
lean_dec(v_head_809_);
lean_dec(v_x_804_);
lean_dec(v_id_802_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
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
else
{
lean_object* v___x_855_; 
lean_del_object(v___x_812_);
lean_dec(v_tail_810_);
lean_dec(v_head_809_);
lean_dec(v_x_804_);
lean_dec(v_id_802_);
if (v_isShared_834_ == 0)
{
v___x_855_ = v___x_833_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_831_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
else
{
goto v___jp_814_;
}
v___jp_814_:
{
lean_object* v___x_816_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v_x_804_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_head_809_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_x_804_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v_x_803_ = v_tail_810_;
v_x_804_ = v___x_816_;
goto _start;
}
}
v___jp_819_:
{
if (v_a_820_ == 0)
{
lean_del_object(v___x_812_);
lean_dec(v_head_809_);
v_x_803_ = v_tail_810_;
goto _start;
}
else
{
goto v___jp_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_861_, v_x_862_, v_x_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_box(0);
return v___x_869_;
}
else
{
lean_object* v_head_870_; lean_object* v_tail_871_; lean_object* v_fst_872_; uint8_t v___x_873_; 
v_head_870_ = lean_ctor_get(v_x_868_, 0);
v_tail_871_ = lean_ctor_get(v_x_868_, 1);
v_fst_872_ = lean_ctor_get(v_head_870_, 0);
v___x_873_ = l_Lean_isPrivateName(v_fst_872_);
if (v___x_873_ == 0)
{
v_x_868_ = v_tail_871_;
goto _start;
}
else
{
lean_object* v___x_875_; 
lean_inc(v_head_870_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v_head_870_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_876_);
lean_dec(v_x_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = 1;
v___x_883_ = 0;
v___x_884_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_878_, v___x_882_, v___x_883_, v___y_879_, v___y_880_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_options_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_options_893_ = lean_ctor_get(v___y_891_, 2);
v___x_894_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_893_, v_opt_890_);
v___x_895_ = lean_box(v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_897_, v___y_898_);
lean_dec_ref(v___y_898_);
lean_dec_ref(v_opt_897_);
return v_res_900_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_env_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_934_; 
v___x_911_ = lean_st_ref_get(v___y_909_);
v_env_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_env_912_);
lean_dec(v___x_911_);
v___x_913_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_914_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_913_, v___y_908_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_934_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v_isExporting_924_; 
v_isExporting_924_ = lean_ctor_get_uint8(v_env_912_, sizeof(void*)*8);
lean_dec_ref(v_env_912_);
if (v_isExporting_924_ == 0)
{
lean_dec(v_a_915_);
lean_dec(v_id_907_);
goto v___jp_919_;
}
else
{
uint8_t v___x_925_; 
v___x_925_ = l_Lean_isPrivateName(v_id_907_);
if (v___x_925_ == 0)
{
lean_dec(v_a_915_);
lean_dec(v_id_907_);
goto v___jp_919_;
}
else
{
uint8_t v___x_926_; 
v___x_926_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_926_ == 0)
{
lean_dec(v_id_907_);
goto v___jp_919_;
}
else
{
lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_del_object(v___x_917_);
v___x_927_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_928_ = 0;
v___x_929_ = l_Lean_MessageData_ofConstName(v_id_907_, v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_932_, v___y_908_, v___y_909_);
return v___x_933_;
}
}
}
v___jp_919_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_940_, uint8_t v_enableLog_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v_env_946_; lean_object* v_options_947_; lean_object* v_currNamespace_948_; lean_object* v_openDecls_949_; lean_object* v___x_950_; lean_object* v_env_951_; lean_object* v_res_952_; 
v___x_945_ = lean_st_ref_get(v___y_943_);
v_env_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_946_);
lean_dec(v___x_945_);
v_options_947_ = lean_ctor_get(v___y_942_, 2);
v_currNamespace_948_ = lean_ctor_get(v___y_942_, 6);
v_openDecls_949_ = lean_ctor_get(v___y_942_, 7);
v___x_950_ = lean_st_ref_get(v___y_943_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
lean_inc(v_openDecls_949_);
lean_inc(v_currNamespace_948_);
v_res_952_ = l_Lean_ResolveName_resolveGlobalName(v_env_946_, v_options_947_, v_currNamespace_948_, v_openDecls_949_, v_id_940_);
if (v_enableLog_941_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_env_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_res_952_);
return v___x_953_;
}
else
{
uint8_t v_isExporting_954_; 
v_isExporting_954_ = lean_ctor_get_uint8(v_env_951_, sizeof(void*)*8);
lean_dec_ref(v_env_951_);
if (v_isExporting_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_res_952_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_952_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; lean_object* v_fst_958_; lean_object* v___x_959_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_956_, 1);
v_fst_958_ = lean_ctor_get(v_val_957_, 0);
lean_inc(v_fst_958_);
lean_dec(v_val_957_);
v___x_959_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_958_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_959_, 0);
lean_dec(v_unused_967_);
v___x_961_ = v___x_959_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_dec(v___x_959_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_res_952_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_res_952_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_res_952_);
v_a_968_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_959_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_959_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v___x_976_; 
lean_dec(v___x_956_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_res_952_);
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_977_, lean_object* v_enableLog_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_enableLog_boxed_982_; lean_object* v_res_983_; 
v_enableLog_boxed_982_ = lean_unbox(v_enableLog_978_);
v_res_983_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_977_, v_enableLog_boxed_982_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
uint8_t v___x_988_; lean_object* v___x_989_; 
v___x_988_ = 1;
lean_inc(v_id_984_);
v___x_989_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_984_, v___x_988_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_box(0);
v___x_992_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_984_, v_a_990_, v___x_991_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1001_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = l_List_reverse___redArg(v_a_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
return v___x_992_;
}
}
else
{
lean_dec(v_id_984_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_realizeGlobalName(v_id_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1007_, v___y_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_opt_1012_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
if (lean_obj_tag(v_a_1017_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = l_List_reverse___redArg(v_a_1018_);
return v___x_1019_;
}
else
{
lean_object* v_head_1020_; lean_object* v_tail_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1030_; 
v_head_1020_ = lean_ctor_get(v_a_1017_, 0);
v_tail_1021_ = lean_ctor_get(v_a_1017_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1023_ = v_a_1017_;
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_tail_1021_);
lean_inc(v_head_1020_);
lean_dec(v_a_1017_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_fst_1025_; lean_object* v___x_1027_; 
v_fst_1025_ = lean_ctor_get(v_head_1020_, 0);
lean_inc(v_fst_1025_);
lean_dec(v_head_1020_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v_a_1018_);
lean_ctor_set(v___x_1023_, 0, v_fst_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_fst_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1018_);
v___x_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
v_a_1017_ = v_tail_1021_;
v_a_1018_ = v___x_1027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_ref_1035_; lean_object* v___x_1036_; lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
v_ref_1035_ = lean_ctor_get(v___y_1032_, 5);
v___x_1036_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1031_, v___y_1032_, v___y_1033_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_inc(v_ref_1035_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_ref_1035_);
lean_ctor_set(v___x_1041_, 1, v_a_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1051_, lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_fileName_1056_; lean_object* v_fileMap_1057_; lean_object* v_options_1058_; lean_object* v_currRecDepth_1059_; lean_object* v_maxRecDepth_1060_; lean_object* v_ref_1061_; lean_object* v_currNamespace_1062_; lean_object* v_openDecls_1063_; lean_object* v_initHeartbeats_1064_; lean_object* v_maxHeartbeats_1065_; lean_object* v_quotContext_1066_; lean_object* v_currMacroScope_1067_; uint8_t v_diag_1068_; lean_object* v_cancelTk_x3f_1069_; uint8_t v_suppressElabErrors_1070_; lean_object* v_inheritedTraceOptions_1071_; lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_fileName_1056_ = lean_ctor_get(v___y_1053_, 0);
v_fileMap_1057_ = lean_ctor_get(v___y_1053_, 1);
v_options_1058_ = lean_ctor_get(v___y_1053_, 2);
v_currRecDepth_1059_ = lean_ctor_get(v___y_1053_, 3);
v_maxRecDepth_1060_ = lean_ctor_get(v___y_1053_, 4);
v_ref_1061_ = lean_ctor_get(v___y_1053_, 5);
v_currNamespace_1062_ = lean_ctor_get(v___y_1053_, 6);
v_openDecls_1063_ = lean_ctor_get(v___y_1053_, 7);
v_initHeartbeats_1064_ = lean_ctor_get(v___y_1053_, 8);
v_maxHeartbeats_1065_ = lean_ctor_get(v___y_1053_, 9);
v_quotContext_1066_ = lean_ctor_get(v___y_1053_, 10);
v_currMacroScope_1067_ = lean_ctor_get(v___y_1053_, 11);
v_diag_1068_ = lean_ctor_get_uint8(v___y_1053_, sizeof(void*)*14);
v_cancelTk_x3f_1069_ = lean_ctor_get(v___y_1053_, 12);
v_suppressElabErrors_1070_ = lean_ctor_get_uint8(v___y_1053_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1071_ = lean_ctor_get(v___y_1053_, 13);
v_ref_1072_ = l_Lean_replaceRef(v_ref_1051_, v_ref_1061_);
lean_inc_ref(v_inheritedTraceOptions_1071_);
lean_inc(v_cancelTk_x3f_1069_);
lean_inc(v_currMacroScope_1067_);
lean_inc(v_quotContext_1066_);
lean_inc(v_maxHeartbeats_1065_);
lean_inc(v_initHeartbeats_1064_);
lean_inc(v_openDecls_1063_);
lean_inc(v_currNamespace_1062_);
lean_inc(v_maxRecDepth_1060_);
lean_inc(v_currRecDepth_1059_);
lean_inc_ref(v_options_1058_);
lean_inc_ref(v_fileMap_1057_);
lean_inc_ref(v_fileName_1056_);
v___x_1073_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1073_, 0, v_fileName_1056_);
lean_ctor_set(v___x_1073_, 1, v_fileMap_1057_);
lean_ctor_set(v___x_1073_, 2, v_options_1058_);
lean_ctor_set(v___x_1073_, 3, v_currRecDepth_1059_);
lean_ctor_set(v___x_1073_, 4, v_maxRecDepth_1060_);
lean_ctor_set(v___x_1073_, 5, v_ref_1072_);
lean_ctor_set(v___x_1073_, 6, v_currNamespace_1062_);
lean_ctor_set(v___x_1073_, 7, v_openDecls_1063_);
lean_ctor_set(v___x_1073_, 8, v_initHeartbeats_1064_);
lean_ctor_set(v___x_1073_, 9, v_maxHeartbeats_1065_);
lean_ctor_set(v___x_1073_, 10, v_quotContext_1066_);
lean_ctor_set(v___x_1073_, 11, v_currMacroScope_1067_);
lean_ctor_set(v___x_1073_, 12, v_cancelTk_x3f_1069_);
lean_ctor_set(v___x_1073_, 13, v_inheritedTraceOptions_1071_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*14, v_diag_1068_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*14 + 1, v_suppressElabErrors_1070_);
v___x_1074_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1052_, v___x_1073_, v___y_1054_);
lean_dec_ref_known(v___x_1073_, 14);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1075_, v_msg_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_ref_1075_);
return v_res_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1102_, lean_object* v_declHint_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v_env_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_st_ref_get(v___y_1104_);
v_env_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_env_1107_);
lean_dec(v___x_1106_);
v___x_1108_ = l_Lean_Name_isAnonymous(v_declHint_1103_);
if (v___x_1108_ == 0)
{
uint8_t v_isExporting_1109_; 
v_isExporting_1109_ = lean_ctor_get_uint8(v_env_1107_, sizeof(void*)*8);
if (v_isExporting_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_env_1107_);
lean_dec(v_declHint_1103_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_msg_1102_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
lean_inc_ref(v_env_1107_);
v___x_1111_ = l_Lean_Environment_setExporting(v_env_1107_, v___x_1108_);
lean_inc(v_declHint_1103_);
lean_inc_ref(v___x_1111_);
v___x_1112_ = l_Lean_Environment_contains(v___x_1111_, v_declHint_1103_, v_isExporting_1109_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_env_1107_);
lean_dec(v_declHint_1103_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_msg_1102_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_c_1119_; lean_object* v___x_1120_; 
v___x_1114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1116_ = l_Lean_Options_empty;
v___x_1117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1111_);
lean_ctor_set(v___x_1117_, 1, v___x_1114_);
lean_ctor_set(v___x_1117_, 2, v___x_1115_);
lean_ctor_set(v___x_1117_, 3, v___x_1116_);
lean_inc(v_declHint_1103_);
v___x_1118_ = l_Lean_MessageData_ofConstName(v_declHint_1103_, v___x_1108_);
v_c_1119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1119_, 0, v___x_1117_);
lean_ctor_set(v_c_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1107_, v_declHint_1103_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v_env_1107_);
lean_dec(v_declHint_1103_);
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_c_1119_);
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_note(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_msg_1102_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1163_; 
v_val_1128_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1130_ = v___x_1120_;
v_isShared_1131_ = v_isSharedCheck_1163_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v___x_1120_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1163_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_mod_1135_; uint8_t v___x_1136_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Lean_Environment_header(v_env_1107_);
lean_dec_ref(v_env_1107_);
v___x_1134_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1133_);
v_mod_1135_ = lean_array_get(v___x_1132_, v___x_1134_, v_val_1128_);
lean_dec(v_val_1128_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = l_Lean_isPrivateName(v_declHint_1103_);
lean_dec(v_declHint_1103_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_c_1119_);
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_MessageData_ofName(v_mod_1135_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_note(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_msg_1102_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1146_);
v___x_1148_ = v___x_1130_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v_c_1119_);
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofName(v_mod_1135_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_note(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_msg_1102_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1159_);
v___x_1161_ = v___x_1130_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1164_; 
lean_dec_ref(v_env_1107_);
lean_dec(v_declHint_1103_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_msg_1102_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1165_, lean_object* v_declHint_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1165_, v_declHint_1166_, v___y_1167_);
lean_dec(v___y_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1170_, lean_object* v_declHint_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
v___x_1175_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1170_, v_declHint_1171_, v___y_1173_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = l_Lean_unknownIdentifierMessageTag;
v___x_1181_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_a_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1186_, lean_object* v_declHint_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1186_, v_declHint_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1192_, lean_object* v_msg_1193_, lean_object* v_declHint_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1200_; 
v___x_1198_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1193_, v_declHint_1194_, v___y_1195_, v___y_1196_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1192_, v_a_1199_, v___y_1195_, v___y_1196_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1201_, lean_object* v_msg_1202_, lean_object* v_declHint_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1201_, v_msg_1202_, v_declHint_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v_ref_1201_);
return v_res_1207_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1213_ = l_Lean_stringToMessageData(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1214_, lean_object* v_constName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1219_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1220_ = 0;
lean_inc(v_constName_1215_);
v___x_1221_ = l_Lean_MessageData_ofConstName(v_constName_1215_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1214_, v___x_1224_, v_constName_1215_, v___y_1216_, v___y_1217_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1226_, lean_object* v_constName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1226_, v_constName_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v_ref_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = l_List_reverse___redArg(v_a_1233_);
return v___x_1234_;
}
else
{
lean_object* v_head_1235_; lean_object* v_tail_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1247_; 
v_head_1235_ = lean_ctor_get(v_a_1232_, 0);
v_tail_1236_ = lean_ctor_get(v_a_1232_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1232_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1238_ = v_a_1232_;
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_tail_1236_);
lean_inc(v_head_1235_);
lean_dec(v_a_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_snd_1240_; uint8_t v___x_1241_; 
v_snd_1240_ = lean_ctor_get(v_head_1235_, 1);
v___x_1241_ = l_List_isEmpty___redArg(v_snd_1240_);
if (v___x_1241_ == 0)
{
lean_del_object(v___x_1238_);
lean_dec(v_head_1235_);
v_a_1232_ = v_tail_1236_;
goto _start;
}
else
{
lean_object* v___x_1244_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_a_1233_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_head_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_a_1233_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
v_a_1232_ = v_tail_1236_;
v_a_1233_ = v___x_1244_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1248_, lean_object* v_cs_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_cs_1254_; uint8_t v___x_1258_; 
v___x_1253_ = lean_box(0);
v_cs_1254_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1249_, v___x_1253_);
v___x_1258_ = l_List_isEmpty___redArg(v_cs_1254_);
if (v___x_1258_ == 0)
{
lean_dec(v_n_1248_);
goto v___jp_1255_;
}
else
{
lean_object* v_ref_1259_; lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_cs_1254_);
v_ref_1259_ = lean_ctor_get(v___y_1250_, 5);
v___x_1260_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1259_, v_n_1248_, v___y_1250_, v___y_1251_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
v___jp_1255_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1254_, v___x_1253_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1269_, lean_object* v_cs_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1269_, v_cs_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
lean_inc(v_n_1275_);
v___x_1279_ = l_Lean_realizeGlobalName(v_n_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1275_, v_a_1280_, v_a_1276_, v_a_1277_);
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_n_1275_);
v_a_1282_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1279_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1279_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_realizeGlobalConstCore(v_n_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1295_, lean_object* v_ref_1296_, lean_object* v_constName_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1296_, v_constName_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1302_, v_ref_1303_, v_constName_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v_ref_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1309_, lean_object* v_ref_1310_, lean_object* v_msg_1311_, lean_object* v_declHint_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1310_, v_msg_1311_, v_declHint_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_ref_1318_, lean_object* v_msg_1319_, lean_object* v_declHint_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1317_, v_ref_1318_, v_msg_1319_, v_declHint_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v_ref_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1325_, lean_object* v_declHint_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1325_, v_declHint_1326_, v___y_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1331_, lean_object* v_declHint_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1331_, v_declHint_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1337_, lean_object* v_ref_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1338_, v_msg_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_ref_1345_, lean_object* v_msg_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1344_, v_ref_1345_, v_msg_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v_ref_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1351_, lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1352_, v___y_1353_, v___y_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_msg_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1357_, v_msg_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
if (lean_obj_tag(v_a_1363_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = l_List_reverse___redArg(v_a_1364_);
return v___x_1365_;
}
else
{
lean_object* v_head_1366_; lean_object* v_tail_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1376_; 
v_head_1366_ = lean_ctor_get(v_a_1363_, 0);
v_tail_1367_ = lean_ctor_get(v_a_1363_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_1363_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1369_ = v_a_1363_;
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_tail_1367_);
lean_inc(v_head_1366_);
lean_dec(v_a_1363_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Lean_MessageData_ofExpr(v_head_1366_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_a_1364_);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_a_1364_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v_a_1363_ = v_tail_1367_;
v_a_1364_ = v___x_1373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
if (lean_obj_tag(v_a_1377_) == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = l_List_reverse___redArg(v_a_1378_);
return v___x_1379_;
}
else
{
lean_object* v_head_1380_; lean_object* v_tail_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v_head_1380_ = lean_ctor_get(v_a_1377_, 0);
v_tail_1381_ = lean_ctor_get(v_a_1377_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_a_1377_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1383_ = v_a_1377_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_tail_1381_);
lean_inc(v_head_1380_);
lean_dec(v_a_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Lean_mkConst(v_head_1380_, v___x_1385_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_a_1378_);
lean_ctor_set(v___x_1383_, 0, v___x_1386_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_a_1378_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v_a_1377_ = v_tail_1381_;
v_a_1378_ = v___x_1388_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1394_ = l_Lean_stringToMessageData(v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1398_, lean_object* v_cs_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
if (lean_obj_tag(v_cs_1399_) == 1)
{
lean_object* v_tail_1415_; 
v_tail_1415_ = lean_ctor_get(v_cs_1399_, 1);
if (lean_obj_tag(v_tail_1415_) == 0)
{
lean_object* v_head_1416_; lean_object* v___x_1417_; 
lean_dec(v_n_1398_);
v_head_1416_ = lean_ctor_get(v_cs_1399_, 0);
lean_inc(v_head_1416_);
lean_dec_ref_known(v_cs_1399_, 2);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_head_1416_);
return v___x_1417_;
}
else
{
goto v___jp_1403_;
}
}
else
{
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1404_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1405_ = l_Lean_MessageData_ofName(v_n_1398_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_box(0);
v___x_1410_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1399_, v___x_1409_);
v___x_1411_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1410_, v___x_1409_);
v___x_1412_ = l_Lean_MessageData_ofList(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1408_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1413_, v___y_1400_, v___y_1401_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1418_, lean_object* v_cs_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1418_, v_cs_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1428_; 
lean_inc(v_n_1424_);
v___x_1428_ = l_Lean_realizeGlobalConstCore(v_n_1424_, v_a_1425_, v_a_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1424_, v_a_1429_, v_a_1425_, v_a_1426_);
return v___x_1430_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_n_1424_);
v_a_1431_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1428_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
if (lean_obj_tag(v_a_1444_) == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_array_to_list(v_a_1445_);
return v___x_1446_;
}
else
{
lean_object* v_head_1447_; 
v_head_1447_ = lean_ctor_get(v_a_1444_, 0);
if (lean_obj_tag(v_head_1447_) == 1)
{
lean_object* v_fields_1448_; 
v_fields_1448_ = lean_ctor_get(v_head_1447_, 1);
if (lean_obj_tag(v_fields_1448_) == 0)
{
lean_object* v_tail_1449_; lean_object* v_n_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v_head_1447_);
v_tail_1449_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_tail_1449_);
lean_dec_ref_known(v_a_1444_, 2);
v_n_1450_ = lean_ctor_get(v_head_1447_, 0);
lean_inc(v_n_1450_);
lean_dec_ref_known(v_head_1447_, 2);
v___x_1451_ = lean_array_push(v_a_1445_, v_n_1450_);
v_a_1444_ = v_tail_1449_;
v_a_1445_ = v___x_1451_;
goto _start;
}
else
{
lean_object* v_tail_1453_; 
v_tail_1453_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_tail_1453_);
lean_dec_ref_known(v_a_1444_, 2);
v_a_1444_ = v_tail_1453_;
goto _start;
}
}
else
{
lean_object* v_tail_1455_; 
v_tail_1455_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_tail_1455_);
lean_dec_ref_known(v_a_1444_, 2);
v_a_1444_ = v_tail_1455_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1464_, lean_object* v_k_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
if (lean_obj_tag(v_stx_1464_) == 3)
{
lean_object* v_val_1469_; lean_object* v_preresolved_1470_; lean_object* v___x_1471_; lean_object* v_pre_1472_; uint8_t v___x_1473_; 
v_val_1469_ = lean_ctor_get(v_stx_1464_, 2);
lean_inc(v_val_1469_);
v_preresolved_1470_ = lean_ctor_get(v_stx_1464_, 3);
v___x_1471_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1470_);
v_pre_1472_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1470_, v___x_1471_);
v___x_1473_ = l_List_isEmpty___redArg(v_pre_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec(v_val_1469_);
lean_dec_ref_known(v_stx_1464_, 4);
lean_dec_ref(v_k_1465_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_pre_1472_);
return v___x_1474_;
}
else
{
lean_object* v_fileName_1475_; lean_object* v_fileMap_1476_; lean_object* v_options_1477_; lean_object* v_currRecDepth_1478_; lean_object* v_maxRecDepth_1479_; lean_object* v_ref_1480_; lean_object* v_currNamespace_1481_; lean_object* v_openDecls_1482_; lean_object* v_initHeartbeats_1483_; lean_object* v_maxHeartbeats_1484_; lean_object* v_quotContext_1485_; lean_object* v_currMacroScope_1486_; uint8_t v_diag_1487_; lean_object* v_cancelTk_x3f_1488_; uint8_t v_suppressElabErrors_1489_; lean_object* v_inheritedTraceOptions_1490_; lean_object* v_ref_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_pre_1472_);
v_fileName_1475_ = lean_ctor_get(v___y_1466_, 0);
v_fileMap_1476_ = lean_ctor_get(v___y_1466_, 1);
v_options_1477_ = lean_ctor_get(v___y_1466_, 2);
v_currRecDepth_1478_ = lean_ctor_get(v___y_1466_, 3);
v_maxRecDepth_1479_ = lean_ctor_get(v___y_1466_, 4);
v_ref_1480_ = lean_ctor_get(v___y_1466_, 5);
v_currNamespace_1481_ = lean_ctor_get(v___y_1466_, 6);
v_openDecls_1482_ = lean_ctor_get(v___y_1466_, 7);
v_initHeartbeats_1483_ = lean_ctor_get(v___y_1466_, 8);
v_maxHeartbeats_1484_ = lean_ctor_get(v___y_1466_, 9);
v_quotContext_1485_ = lean_ctor_get(v___y_1466_, 10);
v_currMacroScope_1486_ = lean_ctor_get(v___y_1466_, 11);
v_diag_1487_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*14);
v_cancelTk_x3f_1488_ = lean_ctor_get(v___y_1466_, 12);
v_suppressElabErrors_1489_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1490_ = lean_ctor_get(v___y_1466_, 13);
v_ref_1491_ = l_Lean_replaceRef(v_stx_1464_, v_ref_1480_);
lean_dec_ref_known(v_stx_1464_, 4);
lean_inc_ref(v_inheritedTraceOptions_1490_);
lean_inc(v_cancelTk_x3f_1488_);
lean_inc(v_currMacroScope_1486_);
lean_inc(v_quotContext_1485_);
lean_inc(v_maxHeartbeats_1484_);
lean_inc(v_initHeartbeats_1483_);
lean_inc(v_openDecls_1482_);
lean_inc(v_currNamespace_1481_);
lean_inc(v_maxRecDepth_1479_);
lean_inc(v_currRecDepth_1478_);
lean_inc_ref(v_options_1477_);
lean_inc_ref(v_fileMap_1476_);
lean_inc_ref(v_fileName_1475_);
v___x_1492_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1492_, 0, v_fileName_1475_);
lean_ctor_set(v___x_1492_, 1, v_fileMap_1476_);
lean_ctor_set(v___x_1492_, 2, v_options_1477_);
lean_ctor_set(v___x_1492_, 3, v_currRecDepth_1478_);
lean_ctor_set(v___x_1492_, 4, v_maxRecDepth_1479_);
lean_ctor_set(v___x_1492_, 5, v_ref_1491_);
lean_ctor_set(v___x_1492_, 6, v_currNamespace_1481_);
lean_ctor_set(v___x_1492_, 7, v_openDecls_1482_);
lean_ctor_set(v___x_1492_, 8, v_initHeartbeats_1483_);
lean_ctor_set(v___x_1492_, 9, v_maxHeartbeats_1484_);
lean_ctor_set(v___x_1492_, 10, v_quotContext_1485_);
lean_ctor_set(v___x_1492_, 11, v_currMacroScope_1486_);
lean_ctor_set(v___x_1492_, 12, v_cancelTk_x3f_1488_);
lean_ctor_set(v___x_1492_, 13, v_inheritedTraceOptions_1490_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*14, v_diag_1487_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*14 + 1, v_suppressElabErrors_1489_);
lean_inc(v___y_1467_);
v___x_1493_ = lean_apply_4(v_k_1465_, v_val_1469_, v___x_1492_, v___y_1467_, lean_box(0));
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref(v_k_1465_);
v___x_1494_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1464_, v___x_1494_, v___y_1466_, v___y_1467_);
lean_dec(v_stx_1464_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1496_, lean_object* v_k_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1496_, v_k_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_fileName_1507_; lean_object* v_fileMap_1508_; lean_object* v_options_1509_; lean_object* v_currRecDepth_1510_; lean_object* v_maxRecDepth_1511_; lean_object* v_ref_1512_; lean_object* v_currNamespace_1513_; lean_object* v_openDecls_1514_; lean_object* v_initHeartbeats_1515_; lean_object* v_maxHeartbeats_1516_; lean_object* v_quotContext_1517_; lean_object* v_currMacroScope_1518_; uint8_t v_diag_1519_; lean_object* v_cancelTk_x3f_1520_; uint8_t v_suppressElabErrors_1521_; lean_object* v_inheritedTraceOptions_1522_; lean_object* v___x_1523_; lean_object* v_ref_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_fileName_1507_ = lean_ctor_get(v_a_1504_, 0);
v_fileMap_1508_ = lean_ctor_get(v_a_1504_, 1);
v_options_1509_ = lean_ctor_get(v_a_1504_, 2);
v_currRecDepth_1510_ = lean_ctor_get(v_a_1504_, 3);
v_maxRecDepth_1511_ = lean_ctor_get(v_a_1504_, 4);
v_ref_1512_ = lean_ctor_get(v_a_1504_, 5);
v_currNamespace_1513_ = lean_ctor_get(v_a_1504_, 6);
v_openDecls_1514_ = lean_ctor_get(v_a_1504_, 7);
v_initHeartbeats_1515_ = lean_ctor_get(v_a_1504_, 8);
v_maxHeartbeats_1516_ = lean_ctor_get(v_a_1504_, 9);
v_quotContext_1517_ = lean_ctor_get(v_a_1504_, 10);
v_currMacroScope_1518_ = lean_ctor_get(v_a_1504_, 11);
v_diag_1519_ = lean_ctor_get_uint8(v_a_1504_, sizeof(void*)*14);
v_cancelTk_x3f_1520_ = lean_ctor_get(v_a_1504_, 12);
v_suppressElabErrors_1521_ = lean_ctor_get_uint8(v_a_1504_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1522_ = lean_ctor_get(v_a_1504_, 13);
v___x_1523_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1524_ = l_Lean_replaceRef(v_stx_1503_, v_ref_1512_);
lean_inc_ref(v_inheritedTraceOptions_1522_);
lean_inc(v_cancelTk_x3f_1520_);
lean_inc(v_currMacroScope_1518_);
lean_inc(v_quotContext_1517_);
lean_inc(v_maxHeartbeats_1516_);
lean_inc(v_initHeartbeats_1515_);
lean_inc(v_openDecls_1514_);
lean_inc(v_currNamespace_1513_);
lean_inc(v_maxRecDepth_1511_);
lean_inc(v_currRecDepth_1510_);
lean_inc_ref(v_options_1509_);
lean_inc_ref(v_fileMap_1508_);
lean_inc_ref(v_fileName_1507_);
v___x_1525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1525_, 0, v_fileName_1507_);
lean_ctor_set(v___x_1525_, 1, v_fileMap_1508_);
lean_ctor_set(v___x_1525_, 2, v_options_1509_);
lean_ctor_set(v___x_1525_, 3, v_currRecDepth_1510_);
lean_ctor_set(v___x_1525_, 4, v_maxRecDepth_1511_);
lean_ctor_set(v___x_1525_, 5, v_ref_1524_);
lean_ctor_set(v___x_1525_, 6, v_currNamespace_1513_);
lean_ctor_set(v___x_1525_, 7, v_openDecls_1514_);
lean_ctor_set(v___x_1525_, 8, v_initHeartbeats_1515_);
lean_ctor_set(v___x_1525_, 9, v_maxHeartbeats_1516_);
lean_ctor_set(v___x_1525_, 10, v_quotContext_1517_);
lean_ctor_set(v___x_1525_, 11, v_currMacroScope_1518_);
lean_ctor_set(v___x_1525_, 12, v_cancelTk_x3f_1520_);
lean_ctor_set(v___x_1525_, 13, v_inheritedTraceOptions_1522_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*14, v_diag_1519_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*14 + 1, v_suppressElabErrors_1521_);
v___x_1526_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1503_, v___x_1523_, v___x_1525_, v_a_1505_);
lean_dec_ref_known(v___x_1525_, 14);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_realizeGlobalConst(v_stx_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1531_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_instMonadEIO(lean_box(0));
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_toApplicative_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1572_; 
v___x_1539_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1540_ = l_StateRefT_x27_instMonad___redArg(v___x_1539_);
v_toApplicative_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v___x_1540_, 1);
lean_dec(v_unused_1573_);
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1572_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_toApplicative_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1572_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_toFunctor_1545_; lean_object* v_toSeq_1546_; lean_object* v_toSeqLeft_1547_; lean_object* v_toSeqRight_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1570_; 
v_toFunctor_1545_ = lean_ctor_get(v_toApplicative_1541_, 0);
v_toSeq_1546_ = lean_ctor_get(v_toApplicative_1541_, 2);
v_toSeqLeft_1547_ = lean_ctor_get(v_toApplicative_1541_, 3);
v_toSeqRight_1548_ = lean_ctor_get(v_toApplicative_1541_, 4);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_toApplicative_1541_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_toApplicative_1541_, 1);
lean_dec(v_unused_1571_);
v___x_1550_ = v_toApplicative_1541_;
v_isShared_1551_ = v_isSharedCheck_1570_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_toSeqRight_1548_);
lean_inc(v_toSeqLeft_1547_);
lean_inc(v_toSeq_1546_);
lean_inc(v_toFunctor_1545_);
lean_dec(v_toApplicative_1541_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1570_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1561_; 
v___f_1552_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1553_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1545_);
v___f_1554_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1554_, 0, v_toFunctor_1545_);
v___f_1555_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1555_, 0, v_toFunctor_1545_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___f_1554_);
lean_ctor_set(v___x_1556_, 1, v___f_1555_);
v___f_1557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1557_, 0, v_toSeqRight_1548_);
v___f_1558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1558_, 0, v_toSeqLeft_1547_);
v___f_1559_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1559_, 0, v_toSeq_1546_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___f_1557_);
lean_ctor_set(v___x_1550_, 3, v___f_1558_);
lean_ctor_set(v___x_1550_, 2, v___f_1559_);
lean_ctor_set(v___x_1550_, 1, v___f_1552_);
lean_ctor_set(v___x_1550_, 0, v___x_1556_);
v___x_1561_ = v___x_1550_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___f_1552_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v___f_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v___f_1558_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v___f_1557_);
v___x_1561_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___f_1553_);
lean_ctor_set(v___x_1543_, 0, v___x_1561_);
v___x_1563_ = v___x_1543_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___f_1553_);
v___x_1563_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_195__overap_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_instInhabitedOfMonad___redArg(v___x_1563_, v___x_1564_);
v___x_195__overap_1566_ = lean_panic_fn_borrowed(v___x_1565_, v_msg_1535_);
lean_dec(v___x_1565_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
v___x_1567_ = lean_apply_3(v___x_195__overap_1566_, v___y_1536_, v___y_1537_, lean_box(0));
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
return v_x_1580_;
}
else
{
lean_object* v_head_1582_; lean_object* v_tail_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_head_1582_ = lean_ctor_get(v_x_1581_, 0);
v_tail_1583_ = lean_ctor_get(v_x_1581_, 1);
v___x_1584_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1585_ = lean_string_append(v_x_1580_, v___x_1584_);
v___x_1586_ = lean_expr_dbg_to_string(v_head_1582_);
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
lean_dec_ref(v___x_1586_);
v_x_1580_ = v___x_1587_;
v_x_1581_ = v_tail_1583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1589_, v_x_1590_);
lean_dec(v_x_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1595_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1596_;
}
else
{
lean_object* v_tail_1597_; 
v_tail_1597_ = lean_ctor_get(v_x_1595_, 1);
if (lean_obj_tag(v_tail_1597_) == 0)
{
lean_object* v_head_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_head_1598_ = lean_ctor_get(v_x_1595_, 0);
v___x_1599_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1600_ = lean_expr_dbg_to_string(v_head_1598_);
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v_head_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint32_t v___x_1609_; lean_object* v___x_1610_; 
v_head_1604_ = lean_ctor_get(v_x_1595_, 0);
v___x_1605_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1606_ = lean_expr_dbg_to_string(v_head_1604_);
v___x_1607_ = lean_string_append(v___x_1605_, v___x_1606_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1607_, v_tail_1597_);
v___x_1609_ = 93;
v___x_1610_ = lean_string_push(v___x_1608_, v___x_1609_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1611_);
lean_dec(v_x_1611_);
return v_res_1612_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1616_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1617_ = lean_unsigned_to_nat(11u);
v___x_1618_ = lean_unsigned_to_nat(429u);
v___x_1619_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1620_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1621_ = l_mkPanicMessageWithDecl(v___x_1620_, v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1624_, lean_object* v_cs_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
if (lean_obj_tag(v_cs_1625_) == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_id_1624_);
v___x_1629_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1630_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1629_, v___y_1626_, v___y_1627_);
return v___x_1630_;
}
else
{
lean_object* v_tail_1631_; 
v_tail_1631_ = lean_ctor_get(v_cs_1625_, 1);
if (lean_obj_tag(v_tail_1631_) == 0)
{
lean_object* v_head_1632_; lean_object* v___x_1633_; 
lean_dec(v_id_1624_);
v_head_1632_ = lean_ctor_get(v_cs_1625_, 0);
lean_inc(v_head_1632_);
lean_dec_ref_known(v_cs_1625_, 2);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_head_1632_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1634_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1635_ = lean_box(0);
v___x_1636_ = 0;
lean_inc(v_id_1624_);
v___x_1637_ = l_Lean_Syntax_formatStx(v_id_1624_, v___x_1635_, v___x_1636_);
v___x_1638_ = l_Std_Format_defWidth;
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = l_Std_Format_pretty(v___x_1637_, v___x_1638_, v___x_1639_, v___x_1639_);
v___x_1641_ = lean_string_append(v___x_1634_, v___x_1640_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1643_ = lean_string_append(v___x_1641_, v___x_1642_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1625_, v___x_1644_);
v___x_1646_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1645_);
lean_dec(v___x_1645_);
v___x_1647_ = lean_string_append(v___x_1643_, v___x_1646_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_ofFormat(v___x_1648_);
v___x_1650_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1624_, v___x_1649_, v___y_1626_, v___y_1627_);
lean_dec(v_id_1624_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1651_, lean_object* v_cs_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1651_, v_cs_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
lean_inc(v_id_1657_);
v___x_1661_ = l_Lean_realizeGlobalConst(v_id_1657_, v_a_1658_, v_a_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1657_, v_a_1662_, v_a_1658_, v_a_1659_);
return v___x_1663_;
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_id_1657_);
v_a_1664_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1661_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1661_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_realizeGlobalConstNoOverload(v_id_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1676_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(3863082579u);
v___x_1709_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1710_ = l_Lean_Name_num___override(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1713_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1714_ = l_Lean_Name_str___override(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1717_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1718_ = l_Lean_Name_str___override(v___x_1717_, v___x_1716_);
return v___x_1718_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_unsigned_to_nat(2u);
v___x_1720_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1721_ = l_Lean_Name_num___override(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1723_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1724_ = 0;
v___x_1725_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1726_ = l_Lean_registerTraceClass(v___x_1723_, v___x_1724_, v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1728_;
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

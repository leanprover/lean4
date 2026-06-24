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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object*);
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
lean_dec_ref_known(v___x_134_, 1);
if (lean_obj_tag(v_val_135_) == 3)
{
lean_object* v_v_136_; 
v_v_136_ = lean_ctor_get(v_val_135_, 0);
lean_inc(v_v_136_);
lean_dec_ref_known(v_val_135_, 1);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__0);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_ctor_set(v___x_145_, 3, v___x_144_);
lean_ctor_set(v___x_145_, 4, v___x_143_);
lean_ctor_set(v___x_145_, 5, v___x_143_);
lean_ctor_set(v___x_145_, 6, v___x_143_);
lean_ctor_set(v___x_145_, 7, v___x_143_);
lean_ctor_set(v___x_145_, 8, v___x_143_);
lean_ctor_set(v___x_145_, 9, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(32u);
v___x_147_ = lean_mk_empty_array_with_capacity(v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4(void){
_start:
{
size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = ((size_t)5ULL);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_unsigned_to_nat(32u);
v___x_152_ = lean_mk_empty_array_with_capacity(v___x_151_);
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__3);
v___x_154_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_150_);
lean_ctor_set(v___x_154_, 3, v___x_150_);
lean_ctor_set_usize(v___x_154_, 4, v___x_149_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = lean_box(1);
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__4);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__1);
v___x_158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(lean_object* v_msgData_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v_env_164_; lean_object* v_options_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_163_ = lean_st_ref_get(v___y_161_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v_options_165_ = lean_ctor_get(v___y_160_, 2);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_165_);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v_env_164_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set(v___x_168_, 3, v_options_165_);
v___x_169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_msgData_159_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___boxed(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msgData_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(size_t v_sz_176_, size_t v_i_177_, lean_object* v_bs_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_179_ == 0)
{
return v_bs_178_;
}
else
{
lean_object* v_v_180_; lean_object* v_msg_181_; lean_object* v___x_182_; lean_object* v_bs_x27_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; 
v_v_180_ = lean_array_uget_borrowed(v_bs_178_, v_i_177_);
v_msg_181_ = lean_ctor_get(v_v_180_, 1);
lean_inc_ref(v_msg_181_);
v___x_182_ = lean_unsigned_to_nat(0u);
v_bs_x27_183_ = lean_array_uset(v_bs_178_, v_i_177_, v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_add(v_i_177_, v___x_184_);
v___x_186_ = lean_array_uset(v_bs_x27_183_, v_i_177_, v_msg_181_);
v_i_177_ = v___x_185_;
v_bs_178_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_188_, lean_object* v_i_189_, lean_object* v_bs_190_){
_start:
{
size_t v_sz_boxed_191_; size_t v_i_boxed_192_; lean_object* v_res_193_; 
v_sz_boxed_191_ = lean_unbox_usize(v_sz_188_);
lean_dec(v_sz_188_);
v_i_boxed_192_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_boxed_191_, v_i_boxed_192_, v_bs_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(lean_object* v_oldTraces_194_, lean_object* v_data_195_, lean_object* v_ref_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_fileName_201_; lean_object* v_fileMap_202_; lean_object* v_options_203_; lean_object* v_currRecDepth_204_; lean_object* v_maxRecDepth_205_; lean_object* v_ref_206_; lean_object* v_currNamespace_207_; lean_object* v_openDecls_208_; lean_object* v_initHeartbeats_209_; lean_object* v_maxHeartbeats_210_; lean_object* v_quotContext_211_; lean_object* v_currMacroScope_212_; uint8_t v_diag_213_; lean_object* v_cancelTk_x3f_214_; uint8_t v_suppressElabErrors_215_; lean_object* v_inheritedTraceOptions_216_; lean_object* v___x_217_; lean_object* v_traceState_218_; lean_object* v_traces_219_; lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_225_; lean_object* v_msg_226_; lean_object* v___x_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_265_; 
v_fileName_201_ = lean_ctor_get(v___y_198_, 0);
v_fileMap_202_ = lean_ctor_get(v___y_198_, 1);
v_options_203_ = lean_ctor_get(v___y_198_, 2);
v_currRecDepth_204_ = lean_ctor_get(v___y_198_, 3);
v_maxRecDepth_205_ = lean_ctor_get(v___y_198_, 4);
v_ref_206_ = lean_ctor_get(v___y_198_, 5);
v_currNamespace_207_ = lean_ctor_get(v___y_198_, 6);
v_openDecls_208_ = lean_ctor_get(v___y_198_, 7);
v_initHeartbeats_209_ = lean_ctor_get(v___y_198_, 8);
v_maxHeartbeats_210_ = lean_ctor_get(v___y_198_, 9);
v_quotContext_211_ = lean_ctor_get(v___y_198_, 10);
v_currMacroScope_212_ = lean_ctor_get(v___y_198_, 11);
v_diag_213_ = lean_ctor_get_uint8(v___y_198_, sizeof(void*)*14);
v_cancelTk_x3f_214_ = lean_ctor_get(v___y_198_, 12);
v_suppressElabErrors_215_ = lean_ctor_get_uint8(v___y_198_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_216_ = lean_ctor_get(v___y_198_, 13);
v___x_217_ = lean_st_ref_get(v___y_199_);
v_traceState_218_ = lean_ctor_get(v___x_217_, 4);
lean_inc_ref(v_traceState_218_);
lean_dec(v___x_217_);
v_traces_219_ = lean_ctor_get(v_traceState_218_, 0);
lean_inc_ref(v_traces_219_);
lean_dec_ref(v_traceState_218_);
v_ref_220_ = l_Lean_replaceRef(v_ref_196_, v_ref_206_);
lean_inc_ref(v_inheritedTraceOptions_216_);
lean_inc(v_cancelTk_x3f_214_);
lean_inc(v_currMacroScope_212_);
lean_inc(v_quotContext_211_);
lean_inc(v_maxHeartbeats_210_);
lean_inc(v_initHeartbeats_209_);
lean_inc(v_openDecls_208_);
lean_inc(v_currNamespace_207_);
lean_inc(v_maxRecDepth_205_);
lean_inc(v_currRecDepth_204_);
lean_inc_ref(v_options_203_);
lean_inc_ref(v_fileMap_202_);
lean_inc_ref(v_fileName_201_);
v___x_221_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_221_, 0, v_fileName_201_);
lean_ctor_set(v___x_221_, 1, v_fileMap_202_);
lean_ctor_set(v___x_221_, 2, v_options_203_);
lean_ctor_set(v___x_221_, 3, v_currRecDepth_204_);
lean_ctor_set(v___x_221_, 4, v_maxRecDepth_205_);
lean_ctor_set(v___x_221_, 5, v_ref_220_);
lean_ctor_set(v___x_221_, 6, v_currNamespace_207_);
lean_ctor_set(v___x_221_, 7, v_openDecls_208_);
lean_ctor_set(v___x_221_, 8, v_initHeartbeats_209_);
lean_ctor_set(v___x_221_, 9, v_maxHeartbeats_210_);
lean_ctor_set(v___x_221_, 10, v_quotContext_211_);
lean_ctor_set(v___x_221_, 11, v_currMacroScope_212_);
lean_ctor_set(v___x_221_, 12, v_cancelTk_x3f_214_);
lean_ctor_set(v___x_221_, 13, v_inheritedTraceOptions_216_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14, v_diag_213_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14 + 1, v_suppressElabErrors_215_);
v___x_222_ = l_Lean_PersistentArray_toArray___redArg(v_traces_219_);
lean_dec_ref(v_traces_219_);
v_sz_223_ = lean_array_size(v___x_222_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_223_, v___x_224_, v___x_222_);
v_msg_226_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_226_, 0, v_data_195_);
lean_ctor_set(v_msg_226_, 1, v_msg_197_);
lean_ctor_set(v_msg_226_, 2, v___x_225_);
v___x_227_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_226_, v___x_221_, v___y_199_);
lean_dec_ref_known(v___x_221_, 14);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_265_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_265_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_265_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_traceState_233_; lean_object* v_env_234_; lean_object* v_nextMacroScope_235_; lean_object* v_ngen_236_; lean_object* v_auxDeclNGen_237_; lean_object* v_cache_238_; lean_object* v_messages_239_; lean_object* v_infoState_240_; lean_object* v_snapshotTasks_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_264_; 
v___x_232_ = lean_st_ref_take(v___y_199_);
v_traceState_233_ = lean_ctor_get(v___x_232_, 4);
v_env_234_ = lean_ctor_get(v___x_232_, 0);
v_nextMacroScope_235_ = lean_ctor_get(v___x_232_, 1);
v_ngen_236_ = lean_ctor_get(v___x_232_, 2);
v_auxDeclNGen_237_ = lean_ctor_get(v___x_232_, 3);
v_cache_238_ = lean_ctor_get(v___x_232_, 5);
v_messages_239_ = lean_ctor_get(v___x_232_, 6);
v_infoState_240_ = lean_ctor_get(v___x_232_, 7);
v_snapshotTasks_241_ = lean_ctor_get(v___x_232_, 8);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_264_ == 0)
{
v___x_243_ = v___x_232_;
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snapshotTasks_241_);
lean_inc(v_infoState_240_);
lean_inc(v_messages_239_);
lean_inc(v_cache_238_);
lean_inc(v_traceState_233_);
lean_inc(v_auxDeclNGen_237_);
lean_inc(v_ngen_236_);
lean_inc(v_nextMacroScope_235_);
lean_inc(v_env_234_);
lean_dec(v___x_232_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
uint64_t v_tid_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_262_; 
v_tid_245_ = lean_ctor_get_uint64(v_traceState_233_, sizeof(void*)*1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_traceState_233_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_traceState_233_, 0);
lean_dec(v_unused_263_);
v___x_247_ = v_traceState_233_;
v_isShared_248_ = v_isSharedCheck_262_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_traceState_233_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_262_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_ref_196_);
lean_ctor_set(v___x_249_, 1, v_a_228_);
v___x_250_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_194_, v___x_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_250_);
lean_ctor_set_uint64(v_reuseFailAlloc_261_, sizeof(void*)*1, v_tid_245_);
v___x_252_ = v_reuseFailAlloc_261_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 4, v___x_252_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_env_234_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_nextMacroScope_235_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_ngen_236_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_auxDeclNGen_237_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_cache_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 6, v_messages_239_);
lean_ctor_set(v_reuseFailAlloc_260_, 7, v_infoState_240_);
lean_ctor_set(v_reuseFailAlloc_260_, 8, v_snapshotTasks_241_);
v___x_254_ = v_reuseFailAlloc_260_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = lean_st_ref_set(v___y_199_, v___x_254_);
v___x_256_ = lean_box(0);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_256_);
v___x_258_ = v___x_230_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(lean_object* v_oldTraces_266_, lean_object* v_data_267_, lean_object* v_ref_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_266_, v_data_267_, v_ref_268_, v_msg_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v_x_274_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v_x_274_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v_x_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v_x_274_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v_x_274_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v_x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 0);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg___boxed(lean_object* v_x_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_292_);
return v_res_294_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(lean_object* v_e_295_){
_start:
{
if (lean_obj_tag(v_e_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 2;
return v___x_296_;
}
else
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v_e_295_, 0);
v___x_298_ = lean_unbox(v_a_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(lean_object* v_e_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_e_301_);
lean_dec_ref(v_e_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0(void){
_start:
{
lean_object* v___x_304_; double v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_float_of_nat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3(void){
_start:
{
lean_object* v___x_309_; double v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1000u);
v___x_310_ = lean_float_of_nat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(lean_object* v_cls_311_, uint8_t v_collapsed_312_, lean_object* v_tag_313_, lean_object* v_opts_314_, uint8_t v_clsEnabled_315_, lean_object* v_oldTraces_316_, lean_object* v_msg_317_, lean_object* v_resStartStop_318_, lean_object* v___y_319_, lean_object* v___y_320_){
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
v___x_341_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_314_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_359_ = v___x_341_;
goto v___jp_358_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_trace_profiler_useHeartbeats;
v___x_396_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_opts_314_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; double v___x_399_; double v___x_400_; double v___x_401_; 
v___x_397_ = l_Lean_trace_profiler_threshold;
v___x_398_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_314_, v___x_397_);
v___x_399_ = lean_float_of_nat(v___x_398_);
v___x_400_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3);
v___x_401_ = lean_float_div(v___x_399_, v___x_400_);
v___y_390_ = v___x_401_;
goto v___jp_389_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; double v___x_404_; 
v___x_402_ = l_Lean_trace_profiler_threshold;
v___x_403_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_314_, v___x_402_);
v___x_404_ = lean_float_of_nat(v___x_403_);
v___y_390_ = v___x_404_;
goto v___jp_389_;
}
}
v___jp_324_:
{
lean_object* v___x_328_; 
lean_inc(v___y_326_);
v___x_328_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_oldTraces_316_, v_data_327_, v___y_326_, v___y_325_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_322_);
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
v_result_345_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_fst_322_);
v___x_346_ = lean_box(v_result_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0);
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
v___y_325_ = v_a_344_;
v___y_326_ = v___y_343_;
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
v___y_325_ = v_a_344_;
v___y_326_ = v___y_343_;
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
v___x_357_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
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
v___x_384_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_fst_322_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(lean_object* v_cls_405_, lean_object* v_collapsed_406_, lean_object* v_tag_407_, lean_object* v_opts_408_, lean_object* v_clsEnabled_409_, lean_object* v_oldTraces_410_, lean_object* v_msg_411_, lean_object* v_resStartStop_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v_collapsed_boxed_416_; uint8_t v_clsEnabled_boxed_417_; lean_object* v_res_418_; 
v_collapsed_boxed_416_ = lean_unbox(v_collapsed_406_);
v_clsEnabled_boxed_417_ = lean_unbox(v_clsEnabled_409_);
v_res_418_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_405_, v_collapsed_boxed_416_, v_tag_407_, v_opts_408_, v_clsEnabled_boxed_417_, v_oldTraces_410_, v_msg_411_, v_resStartStop_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec_ref(v_opts_408_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(lean_object* v_name_419_, lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_426_ == 0)
{
lean_object* v___x_5305__overap_427_; lean_object* v___x_428_; 
v___x_5305__overap_427_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
lean_inc(v___x_5305__overap_427_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v_name_419_);
v___x_428_ = lean_apply_4(v___x_5305__overap_427_, v_name_419_, v___y_423_, v___y_424_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
size_t v_i_boxed_451_; size_t v_stop_boxed_452_; lean_object* v_res_453_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_452_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_444_, v_as_445_, v_i_boxed_451_, v_stop_boxed_452_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v_as_445_);
return v_res_453_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_462_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_463_ = l_Lean_Name_append(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_464_; double v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1000000000u);
v___x_465_ = lean_float_of_nat(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_options_470_; lean_object* v_inheritedTraceOptions_471_; uint8_t v_hasTrace_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___y_476_; 
v_options_470_ = lean_ctor_get(v_a_467_, 2);
v_inheritedTraceOptions_471_ = lean_ctor_get(v_a_467_, 13);
v_hasTrace_472_ = lean_ctor_get_uint8(v_options_470_, sizeof(void*)*1);
v___x_473_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_474_ = lean_box(0);
if (v_hasTrace_472_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_493_ = lean_st_ref_get(v___x_473_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_array_get_size(v___x_493_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v___x_493_);
lean_dec(v_name_466_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_474_);
return v___x_497_;
}
else
{
if (v___x_496_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v___x_493_);
lean_dec(v_name_466_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_474_);
return v___x_498_;
}
else
{
size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((size_t)0ULL);
v___x_500_ = lean_usize_of_nat(v___x_495_);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_466_, v___x_493_, v___x_499_, v___x_500_, v_a_467_, v_a_468_);
lean_dec(v___x_493_);
v___y_476_ = v___x_501_;
goto v___jp_475_;
}
}
}
else
{
lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v_a_510_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v_a_525_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v_a_531_; lean_object* v___y_541_; lean_object* v___y_542_; uint8_t v_a_543_; 
lean_inc(v_name_466_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_502_, 0, v_name_466_);
v___x_503_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_504_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_505_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_471_, v_options_470_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = l_Lean_trace_profiler;
v___x_588_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_470_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
lean_dec_ref(v___f_502_);
v___x_589_ = lean_st_ref_get(v___x_473_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_get_size(v___x_589_);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v___x_589_);
lean_dec(v_name_466_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_474_);
return v___x_593_;
}
else
{
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v___x_589_);
lean_dec(v_name_466_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_474_);
return v___x_594_;
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((size_t)0ULL);
v___x_596_ = lean_usize_of_nat(v___x_591_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_466_, v___x_589_, v___x_595_, v___x_596_, v_a_467_, v_a_468_);
lean_dec(v___x_589_);
v___y_476_ = v___x_597_;
goto v___jp_475_;
}
}
}
else
{
goto v___jp_546_;
}
}
else
{
goto v___jp_546_;
}
v___jp_507_:
{
lean_object* v___x_511_; double v___x_512_; double v___x_513_; double v___x_514_; double v___x_515_; double v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_511_ = lean_io_mono_nanos_now();
v___x_512_ = lean_float_of_nat(v___y_509_);
v___x_513_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_514_ = lean_float_div(v___x_512_, v___x_513_);
v___x_515_ = lean_float_of_nat(v___x_511_);
v___x_516_ = lean_float_div(v___x_515_, v___x_513_);
v___x_517_ = lean_box_float(v___x_514_);
v___x_518_ = lean_box_float(v___x_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_510_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_503_, v_hasTrace_472_, v___x_504_, v_options_470_, v___x_506_, v___y_508_, v___f_502_, v___x_520_, v_a_467_, v_a_468_);
v___y_476_ = v___x_521_;
goto v___jp_475_;
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(v_a_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___y_508_ = v___y_523_;
v___y_509_ = v___y_524_;
v_a_510_ = v___x_527_;
goto v___jp_507_;
}
v___jp_528_:
{
lean_object* v___x_532_; double v___x_533_; double v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_532_ = lean_io_get_num_heartbeats();
v___x_533_ = lean_float_of_nat(v___y_530_);
v___x_534_ = lean_float_of_nat(v___x_532_);
v___x_535_ = lean_box_float(v___x_533_);
v___x_536_ = lean_box_float(v___x_534_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_a_531_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_503_, v_hasTrace_472_, v___x_504_, v_options_470_, v___x_506_, v___y_529_, v___f_502_, v___x_538_, v_a_467_, v_a_468_);
v___y_476_ = v___x_539_;
goto v___jp_475_;
}
v___jp_540_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_box(v_a_543_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___y_529_ = v___y_541_;
v___y_530_ = v___y_542_;
v_a_531_ = v___x_545_;
goto v___jp_528_;
}
v___jp_546_:
{
lean_object* v___x_547_; lean_object* v_a_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_468_);
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = l_Lean_trace_profiler_useHeartbeats;
v___x_550_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_470_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_551_ = lean_io_mono_nanos_now();
v___x_552_ = lean_st_ref_get(v___x_473_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_array_get_size(v___x_552_);
v___x_555_ = lean_nat_dec_lt(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_name_466_);
v___y_523_ = v_a_548_;
v___y_524_ = v___x_551_;
v_a_525_ = v___x_550_;
goto v___jp_522_;
}
else
{
if (v___x_555_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_name_466_);
v___y_523_ = v_a_548_;
v___y_524_ = v___x_551_;
v_a_525_ = v___x_550_;
goto v___jp_522_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_466_, v___x_552_, v___x_556_, v___x_557_, v_a_467_, v_a_468_);
lean_dec(v___x_552_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_unbox(v_a_559_);
lean_dec(v_a_559_);
v___y_523_ = v_a_548_;
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
v___y_508_ = v_a_548_;
v___y_509_ = v___x_551_;
v_a_510_ = v___x_566_;
goto v___jp_507_;
}
}
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_569_ = lean_io_get_num_heartbeats();
v___x_570_ = lean_st_ref_get(v___x_473_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_array_get_size(v___x_570_);
v___x_573_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v___x_570_);
lean_dec(v_name_466_);
v___y_541_ = v_a_548_;
v___y_542_ = v___x_569_;
v_a_543_ = v___x_573_;
goto v___jp_540_;
}
else
{
if (v___x_573_ == 0)
{
lean_dec(v___x_570_);
lean_dec(v_name_466_);
v___y_541_ = v_a_548_;
v___y_542_ = v___x_569_;
v_a_543_ = v___x_573_;
goto v___jp_540_;
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((size_t)0ULL);
v___x_575_ = lean_usize_of_nat(v___x_572_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_466_, v___x_570_, v___x_574_, v___x_575_, v_a_467_, v_a_468_);
lean_dec(v___x_570_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; uint8_t v___x_578_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = lean_unbox(v_a_577_);
lean_dec(v_a_577_);
v___y_541_ = v_a_548_;
v___y_542_ = v___x_569_;
v_a_543_ = v___x_578_;
goto v___jp_540_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_a_579_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_576_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_576_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_529_ = v_a_548_;
v___y_530_ = v___x_569_;
v_a_531_ = v___x_584_;
goto v___jp_528_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_executeReservedNameAction(v_name_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_604_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_609_, lean_object* v_x_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_609_, v_x_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_622_, uint8_t v_suppressElabErrors_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 1)
{
lean_object* v_pre_625_; 
v_pre_625_ = lean_ctor_get(v_x_624_, 0);
switch(lean_obj_tag(v_pre_625_))
{
case 1:
{
lean_object* v_pre_626_; 
v_pre_626_ = lean_ctor_get(v_pre_625_, 0);
switch(lean_obj_tag(v_pre_626_))
{
case 0:
{
lean_object* v_str_627_; lean_object* v_str_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_str_627_ = lean_ctor_get(v_x_624_, 1);
v_str_628_ = lean_ctor_get(v_pre_625_, 1);
v___x_629_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_630_ = lean_string_dec_eq(v_str_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_632_ = lean_string_dec_eq(v_str_628_, v___x_631_);
if (v___x_632_ == 0)
{
return v___y_622_;
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_634_ = lean_string_dec_eq(v_str_627_, v___x_633_);
if (v___x_634_ == 0)
{
return v___y_622_;
}
else
{
return v_suppressElabErrors_623_;
}
}
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_636_ = lean_string_dec_eq(v_str_627_, v___x_635_);
if (v___x_636_ == 0)
{
return v___y_622_;
}
else
{
return v_suppressElabErrors_623_;
}
}
}
case 1:
{
lean_object* v_pre_637_; 
v_pre_637_ = lean_ctor_get(v_pre_626_, 0);
if (lean_obj_tag(v_pre_637_) == 0)
{
lean_object* v_str_638_; lean_object* v_str_639_; lean_object* v_str_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_str_638_ = lean_ctor_get(v_x_624_, 1);
v_str_639_ = lean_ctor_get(v_pre_625_, 1);
v_str_640_ = lean_ctor_get(v_pre_626_, 1);
v___x_641_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_642_ = lean_string_dec_eq(v_str_640_, v___x_641_);
if (v___x_642_ == 0)
{
return v___y_622_;
}
else
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_644_ = lean_string_dec_eq(v_str_639_, v___x_643_);
if (v___x_644_ == 0)
{
return v___y_622_;
}
else
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_646_ = lean_string_dec_eq(v_str_638_, v___x_645_);
if (v___x_646_ == 0)
{
return v___y_622_;
}
else
{
return v_suppressElabErrors_623_;
}
}
}
}
else
{
return v___y_622_;
}
}
default: 
{
return v___y_622_;
}
}
}
case 0:
{
lean_object* v_str_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_str_647_ = lean_ctor_get(v_x_624_, 1);
v___x_648_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_649_ = lean_string_dec_eq(v_str_647_, v___x_648_);
if (v___x_649_ == 0)
{
return v___y_622_;
}
else
{
return v_suppressElabErrors_623_;
}
}
default: 
{
return v___y_622_;
}
}
}
else
{
return v___y_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_650_, lean_object* v_suppressElabErrors_651_, lean_object* v_x_652_){
_start:
{
uint8_t v___y_4708__boxed_653_; uint8_t v_suppressElabErrors_boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v___y_4708__boxed_653_ = lean_unbox(v___y_650_);
v_suppressElabErrors_boxed_654_ = lean_unbox(v_suppressElabErrors_651_);
v_res_655_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4708__boxed_653_, v_suppressElabErrors_boxed_654_, v_x_652_);
lean_dec(v_x_652_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_657_, lean_object* v_msgData_658_, uint8_t v_severity_659_, uint8_t v_isSilent_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_701_; uint8_t v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; lean_object* v___y_737_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___x_748_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; uint8_t v___y_758_; uint8_t v___x_773_; 
v___x_748_ = 2;
v___x_773_ = l_Lean_instBEqMessageSeverity_beq(v_severity_659_, v___x_748_);
if (v___x_773_ == 0)
{
v___y_758_ = v___x_773_;
goto v___jp_757_;
}
else
{
uint8_t v___x_774_; 
lean_inc_ref(v_msgData_658_);
v___x_774_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_658_);
v___y_758_ = v___x_774_;
goto v___jp_757_;
}
v___jp_664_:
{
lean_object* v___x_674_; lean_object* v_currNamespace_675_; lean_object* v_openDecls_676_; lean_object* v_env_677_; lean_object* v_nextMacroScope_678_; lean_object* v_ngen_679_; lean_object* v_auxDeclNGen_680_; lean_object* v_traceState_681_; lean_object* v_cache_682_; lean_object* v_messages_683_; lean_object* v_infoState_684_; lean_object* v_snapshotTasks_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_699_; 
v___x_674_ = lean_st_ref_take(v___y_673_);
v_currNamespace_675_ = lean_ctor_get(v___y_672_, 6);
v_openDecls_676_ = lean_ctor_get(v___y_672_, 7);
v_env_677_ = lean_ctor_get(v___x_674_, 0);
v_nextMacroScope_678_ = lean_ctor_get(v___x_674_, 1);
v_ngen_679_ = lean_ctor_get(v___x_674_, 2);
v_auxDeclNGen_680_ = lean_ctor_get(v___x_674_, 3);
v_traceState_681_ = lean_ctor_get(v___x_674_, 4);
v_cache_682_ = lean_ctor_get(v___x_674_, 5);
v_messages_683_ = lean_ctor_get(v___x_674_, 6);
v_infoState_684_ = lean_ctor_get(v___x_674_, 7);
v_snapshotTasks_685_ = lean_ctor_get(v___x_674_, 8);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_699_ == 0)
{
v___x_687_ = v___x_674_;
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snapshotTasks_685_);
lean_inc(v_infoState_684_);
lean_inc(v_messages_683_);
lean_inc(v_cache_682_);
lean_inc(v_traceState_681_);
lean_inc(v_auxDeclNGen_680_);
lean_inc(v_ngen_679_);
lean_inc(v_nextMacroScope_678_);
lean_inc(v_env_677_);
lean_dec(v___x_674_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_699_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
lean_inc(v_openDecls_676_);
lean_inc(v_currNamespace_675_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_currNamespace_675_);
lean_ctor_set(v___x_689_, 1, v_openDecls_676_);
v___x_690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_666_);
lean_inc_ref(v___y_671_);
lean_inc_ref(v___y_667_);
v___x_691_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_691_, 0, v___y_667_);
lean_ctor_set(v___x_691_, 1, v___y_668_);
lean_ctor_set(v___x_691_, 2, v___y_670_);
lean_ctor_set(v___x_691_, 3, v___y_671_);
lean_ctor_set(v___x_691_, 4, v___x_690_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5, v___y_665_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 1, v___y_669_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 2, v_isSilent_660_);
v___x_692_ = l_Lean_MessageLog_add(v___x_691_, v_messages_683_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 6, v___x_692_);
v___x_694_ = v___x_687_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_env_677_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_nextMacroScope_678_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_ngen_679_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_auxDeclNGen_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_traceState_681_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_cache_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_infoState_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_snapshotTasks_685_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_set(v___y_673_, v___x_694_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
v___jp_700_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_724_; 
v___x_709_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_658_);
v___x_710_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_709_, v___y_661_, v___y_662_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_724_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_724_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_724_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_inc_ref_n(v___y_704_, 2);
v___x_715_ = l_Lean_FileMap_toPosition(v___y_704_, v___y_703_);
lean_dec(v___y_703_);
v___x_716_ = l_Lean_FileMap_toPosition(v___y_704_, v___y_708_);
lean_dec(v___y_708_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_706_ == 0)
{
lean_del_object(v___x_713_);
lean_dec_ref(v___y_701_);
v___y_665_ = v___y_702_;
v___y_666_ = v_a_711_;
v___y_667_ = v___y_705_;
v___y_668_ = v___x_715_;
v___y_669_ = v___y_707_;
v___y_670_ = v___x_717_;
v___y_671_ = v___x_718_;
v___y_672_ = v___y_661_;
v___y_673_ = v___y_662_;
goto v___jp_664_;
}
else
{
uint8_t v___x_719_; 
lean_inc(v_a_711_);
v___x_719_ = l_Lean_MessageData_hasTag(v___y_701_, v_a_711_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec_ref_known(v___x_717_, 1);
lean_dec_ref(v___x_715_);
lean_dec(v_a_711_);
v___x_720_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_720_);
v___x_722_ = v___x_713_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_del_object(v___x_713_);
v___y_665_ = v___y_702_;
v___y_666_ = v_a_711_;
v___y_667_ = v___y_705_;
v___y_668_ = v___x_715_;
v___y_669_ = v___y_707_;
v___y_670_ = v___x_717_;
v___y_671_ = v___x_718_;
v___y_672_ = v___y_661_;
v___y_673_ = v___y_662_;
goto v___jp_664_;
}
}
}
}
v___jp_725_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Syntax_getTailPos_x3f(v___y_727_, v___y_728_);
lean_dec(v___y_727_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_inc(v___y_733_);
v___y_701_ = v___y_726_;
v___y_702_ = v___y_728_;
v___y_703_ = v___y_733_;
v___y_704_ = v___y_729_;
v___y_705_ = v___y_730_;
v___y_706_ = v___y_732_;
v___y_707_ = v___y_731_;
v___y_708_ = v___y_733_;
goto v___jp_700_;
}
else
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___y_701_ = v___y_726_;
v___y_702_ = v___y_728_;
v___y_703_ = v___y_733_;
v___y_704_ = v___y_729_;
v___y_705_ = v___y_730_;
v___y_706_ = v___y_732_;
v___y_707_ = v___y_731_;
v___y_708_ = v_val_735_;
goto v___jp_700_;
}
}
v___jp_736_:
{
lean_object* v_ref_744_; lean_object* v___x_745_; 
v_ref_744_ = l_Lean_replaceRef(v_ref_657_, v___y_739_);
v___x_745_ = l_Lean_Syntax_getPos_x3f(v_ref_744_, v___y_738_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___y_726_ = v___y_737_;
v___y_727_ = v_ref_744_;
v___y_728_ = v___y_738_;
v___y_729_ = v___y_740_;
v___y_730_ = v___y_741_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_742_;
v___y_733_ = v___x_746_;
goto v___jp_725_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_745_, 1);
v___y_726_ = v___y_737_;
v___y_727_ = v_ref_744_;
v___y_728_ = v___y_738_;
v___y_729_ = v___y_740_;
v___y_730_ = v___y_741_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_742_;
v___y_733_ = v_val_747_;
goto v___jp_725_;
}
}
v___jp_749_:
{
if (v___y_756_ == 0)
{
v___y_737_ = v___y_750_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_751_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_753_;
v___y_742_ = v___y_754_;
v___y_743_ = v_severity_659_;
goto v___jp_736_;
}
else
{
v___y_737_ = v___y_750_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_751_;
v___y_740_ = v___y_752_;
v___y_741_ = v___y_753_;
v___y_742_ = v___y_754_;
v___y_743_ = v___x_748_;
goto v___jp_736_;
}
}
v___jp_757_:
{
if (v___y_758_ == 0)
{
lean_object* v_fileName_759_; lean_object* v_fileMap_760_; lean_object* v_options_761_; lean_object* v_ref_762_; uint8_t v_suppressElabErrors_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; uint8_t v___x_767_; uint8_t v___x_768_; 
v_fileName_759_ = lean_ctor_get(v___y_661_, 0);
v_fileMap_760_ = lean_ctor_get(v___y_661_, 1);
v_options_761_ = lean_ctor_get(v___y_661_, 2);
v_ref_762_ = lean_ctor_get(v___y_661_, 5);
v_suppressElabErrors_763_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*14 + 1);
v___x_764_ = lean_box(v___y_758_);
v___x_765_ = lean_box(v_suppressElabErrors_763_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_766_, 0, v___x_764_);
lean_closure_set(v___f_766_, 1, v___x_765_);
v___x_767_ = 1;
v___x_768_ = l_Lean_instBEqMessageSeverity_beq(v_severity_659_, v___x_767_);
if (v___x_768_ == 0)
{
v___y_750_ = v___f_766_;
v___y_751_ = v_ref_762_;
v___y_752_ = v_fileMap_760_;
v___y_753_ = v_fileName_759_;
v___y_754_ = v_suppressElabErrors_763_;
v___y_755_ = v___y_758_;
v___y_756_ = v___x_768_;
goto v___jp_749_;
}
else
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = l_Lean_warningAsError;
v___x_770_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_761_, v___x_769_);
v___y_750_ = v___f_766_;
v___y_751_ = v_ref_762_;
v___y_752_ = v_fileMap_760_;
v___y_753_ = v_fileName_759_;
v___y_754_ = v_suppressElabErrors_763_;
v___y_755_ = v___y_758_;
v___y_756_ = v___x_770_;
goto v___jp_749_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_msgData_658_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_775_, lean_object* v_msgData_776_, lean_object* v_severity_777_, lean_object* v_isSilent_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_severity_boxed_782_; uint8_t v_isSilent_boxed_783_; lean_object* v_res_784_; 
v_severity_boxed_782_ = lean_unbox(v_severity_777_);
v_isSilent_boxed_783_ = lean_unbox(v_isSilent_778_);
v_res_784_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_775_, v_msgData_776_, v_severity_boxed_782_, v_isSilent_boxed_783_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_ref_775_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_785_, uint8_t v_severity_786_, uint8_t v_isSilent_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_ref_791_; lean_object* v___x_792_; 
v_ref_791_ = lean_ctor_get(v___y_788_, 5);
v___x_792_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_791_, v_msgData_785_, v_severity_786_, v_isSilent_787_, v___y_788_, v___y_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_793_, lean_object* v_severity_794_, lean_object* v_isSilent_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v_severity_boxed_799_; uint8_t v_isSilent_boxed_800_; lean_object* v_res_801_; 
v_severity_boxed_799_ = lean_unbox(v_severity_794_);
v_isSilent_boxed_800_ = lean_unbox(v_isSilent_795_);
v_res_801_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_793_, v_severity_boxed_799_, v_isSilent_boxed_800_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = 2;
v___x_807_ = 0;
v___x_808_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_802_, v___x_806_, v___x_807_, v___y_803_, v___y_804_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_813_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v___x_826_; 
lean_dec(v_id_820_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_x_822_);
return v___x_826_;
}
else
{
lean_object* v_head_827_; lean_object* v_tail_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_885_; 
v_head_827_ = lean_ctor_get(v_x_821_, 0);
v_tail_828_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_885_ == 0)
{
v___x_830_ = v_x_821_;
v_isShared_831_ = v_isSharedCheck_885_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_tail_828_);
lean_inc(v_head_827_);
lean_dec(v_x_821_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_885_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_fst_837_; lean_object* v___x_838_; lean_object* v_env_839_; uint8_t v___x_840_; uint8_t v___x_841_; 
v_fst_837_ = lean_ctor_get(v_head_827_, 0);
v___x_838_ = lean_st_ref_get(v___y_824_);
v_env_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc_ref(v_env_839_);
lean_dec(v___x_838_);
v___x_840_ = 1;
lean_inc(v_fst_837_);
v___x_841_ = l_Lean_Environment_contains(v_env_839_, v_fst_837_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_inc(v_fst_837_);
v___x_842_ = l_Lean_executeReservedNameAction(v_fst_837_, v___y_823_, v___y_824_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_843_; lean_object* v_env_844_; uint8_t v___x_845_; 
lean_dec_ref_known(v___x_842_, 1);
v___x_843_ = lean_st_ref_get(v___y_824_);
v_env_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_ref(v_env_844_);
lean_dec(v___x_843_);
v___x_845_ = l_Lean_Environment_containsOnBranch(v_env_844_, v_fst_837_);
lean_dec_ref(v_env_844_);
if (v___x_845_ == 0)
{
lean_del_object(v___x_830_);
lean_dec(v_head_827_);
v_x_821_ = v_tail_828_;
goto _start;
}
else
{
goto v___jp_832_;
}
}
else
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_830_);
v_isSharedCheck_882_ = !lean_is_exclusive(v_head_827_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_883_ = lean_ctor_get(v_head_827_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_head_827_, 0);
lean_dec(v_unused_884_);
v___x_848_ = v_head_827_;
v_isShared_849_ = v_isSharedCheck_882_;
goto v_resetjp_847_;
}
else
{
lean_dec(v_head_827_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_882_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_881_; 
v_a_850_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_881_ == 0)
{
v___x_852_ = v___x_842_;
v_isShared_853_ = v_isSharedCheck_881_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_842_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_881_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___y_855_; uint8_t v___x_879_; 
v___x_879_ = l_Lean_Exception_isInterrupt(v_a_850_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; 
lean_inc(v_a_850_);
v___x_880_ = l_Lean_Exception_isRuntime(v_a_850_);
v___y_855_ = v___x_880_;
goto v___jp_854_;
}
else
{
v___y_855_ = v___x_879_;
goto v___jp_854_;
}
v___jp_854_:
{
if (v___y_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_del_object(v___x_852_);
v___x_856_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_820_);
v___x_857_ = l_Lean_MessageData_ofName(v_id_820_);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 7);
lean_ctor_set(v___x_848_, 1, v___x_857_);
lean_ctor_set(v___x_848_, 0, v___x_856_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_875_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_860_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_Exception_toMessageData(v_a_850_);
v___x_863_ = l_Lean_indentD(v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_864_, v___y_823_, v___y_824_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec_ref_known(v___x_865_, 1);
v_x_821_ = v_tail_828_;
goto _start;
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_tail_828_);
lean_dec(v_x_822_);
lean_dec(v_id_820_);
v_a_867_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
else
{
lean_object* v___x_877_; 
lean_del_object(v___x_848_);
lean_dec(v_tail_828_);
lean_dec(v_x_822_);
lean_dec(v_id_820_);
if (v_isShared_853_ == 0)
{
v___x_877_ = v___x_852_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_850_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
else
{
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v___x_834_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_x_822_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_head_827_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_x_822_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v_x_821_ = v_tail_828_;
v_x_822_ = v___x_834_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_886_, lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_886_, v_x_887_, v_x_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v_fst_897_; uint8_t v___x_898_; 
v_head_895_ = lean_ctor_get(v_x_893_, 0);
v_tail_896_ = lean_ctor_get(v_x_893_, 1);
v_fst_897_ = lean_ctor_get(v_head_895_, 0);
v___x_898_ = l_Lean_isPrivateName(v_fst_897_);
if (v___x_898_ == 0)
{
v_x_893_ = v_tail_896_;
goto _start;
}
else
{
lean_object* v___x_900_; 
lean_inc(v_head_895_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_head_895_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_901_);
lean_dec(v_x_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = 1;
v___x_908_ = 0;
v___x_909_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_903_, v___x_907_, v___x_908_, v___y_904_, v___y_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_options_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_options_918_ = lean_ctor_get(v___y_916_, 2);
v___x_919_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_918_, v_opt_915_);
v___x_920_ = lean_box(v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_922_, v___y_923_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v_opt_922_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v_env_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_959_; 
v___x_936_ = lean_st_ref_get(v___y_934_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_env_937_);
lean_dec(v___x_936_);
v___x_938_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_939_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_938_, v___y_933_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_959_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_959_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_959_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
uint8_t v_isExporting_949_; 
v_isExporting_949_ = lean_ctor_get_uint8(v_env_937_, sizeof(void*)*8);
lean_dec_ref(v_env_937_);
if (v_isExporting_949_ == 0)
{
lean_dec(v_a_940_);
lean_dec(v_id_932_);
goto v___jp_944_;
}
else
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_isPrivateName(v_id_932_);
if (v___x_950_ == 0)
{
lean_dec(v_a_940_);
lean_dec(v_id_932_);
goto v___jp_944_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = lean_unbox(v_a_940_);
lean_dec(v_a_940_);
if (v___x_951_ == 0)
{
lean_dec(v_id_932_);
goto v___jp_944_;
}
else
{
lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_del_object(v___x_942_);
v___x_952_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_953_ = 0;
v___x_954_ = l_Lean_MessageData_ofConstName(v_id_932_, v___x_953_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_957_, v___y_933_, v___y_934_);
return v___x_958_;
}
}
}
v___jp_944_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_box(0);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_965_, uint8_t v_enableLog_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; lean_object* v_options_972_; lean_object* v_currNamespace_973_; lean_object* v_openDecls_974_; lean_object* v___x_975_; lean_object* v_env_976_; lean_object* v_res_977_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v_options_972_ = lean_ctor_get(v___y_967_, 2);
v_currNamespace_973_ = lean_ctor_get(v___y_967_, 6);
v_openDecls_974_ = lean_ctor_get(v___y_967_, 7);
v___x_975_ = lean_st_ref_get(v___y_968_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
lean_inc(v_openDecls_974_);
lean_inc(v_currNamespace_973_);
v_res_977_ = l_Lean_ResolveName_resolveGlobalName(v_env_971_, v_options_972_, v_currNamespace_973_, v_openDecls_974_, v_id_965_);
if (v_enableLog_966_ == 0)
{
lean_object* v___x_978_; 
lean_dec_ref(v_env_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v_res_977_);
return v___x_978_;
}
else
{
uint8_t v_isExporting_979_; 
v_isExporting_979_ = lean_ctor_get_uint8(v_env_976_, sizeof(void*)*8);
lean_dec_ref(v_env_976_);
if (v_isExporting_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_res_977_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_977_);
if (lean_obj_tag(v___x_981_) == 1)
{
lean_object* v_val_982_; lean_object* v_fst_983_; lean_object* v___x_984_; 
v_val_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v___x_981_, 1);
v_fst_983_ = lean_ctor_get(v_val_982_, 0);
lean_inc(v_fst_983_);
lean_dec(v_val_982_);
v___x_984_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_983_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_984_, 0);
lean_dec(v_unused_992_);
v___x_986_ = v___x_984_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_dec(v___x_984_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_res_977_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_res_977_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_res_977_);
v_a_993_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_984_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_984_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v___x_1001_; 
lean_dec(v___x_981_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_res_977_);
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_1002_, lean_object* v_enableLog_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v_enableLog_boxed_1007_; lean_object* v_res_1008_; 
v_enableLog_boxed_1007_ = lean_unbox(v_enableLog_1003_);
v_res_1008_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1002_, v_enableLog_boxed_1007_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = 1;
lean_inc(v_id_1009_);
v___x_1014_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_1009_, v___x_1013_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_box(0);
v___x_1017_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_1009_, v_a_1015_, v___x_1016_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1026_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = l_List_reverse___redArg(v_a_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
return v___x_1017_;
}
}
else
{
lean_dec(v_id_1009_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_realizeGlobalName(v_id_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1032_, v___y_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v_opt_1037_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
if (lean_obj_tag(v_a_1042_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_List_reverse___redArg(v_a_1043_);
return v___x_1044_;
}
else
{
lean_object* v_head_1045_; lean_object* v_tail_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v_head_1045_ = lean_ctor_get(v_a_1042_, 0);
v_tail_1046_ = lean_ctor_get(v_a_1042_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1048_ = v_a_1042_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_tail_1046_);
lean_inc(v_head_1045_);
lean_dec(v_a_1042_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_fst_1050_; lean_object* v___x_1052_; 
v_fst_1050_ = lean_ctor_get(v_head_1045_, 0);
lean_inc(v_fst_1050_);
lean_dec(v_head_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_a_1043_);
lean_ctor_set(v___x_1048_, 0, v_fst_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fst_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_a_1043_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v_a_1042_ = v_tail_1046_;
v_a_1043_ = v___x_1052_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_ref_1060_; lean_object* v___x_1061_; lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_ref_1060_ = lean_ctor_get(v___y_1057_, 5);
v___x_1061_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1056_, v___y_1057_, v___y_1058_);
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_inc(v_ref_1060_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_ref_1060_);
lean_ctor_set(v___x_1066_, 1, v_a_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1076_, lean_object* v_msg_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_fileName_1081_; lean_object* v_fileMap_1082_; lean_object* v_options_1083_; lean_object* v_currRecDepth_1084_; lean_object* v_maxRecDepth_1085_; lean_object* v_ref_1086_; lean_object* v_currNamespace_1087_; lean_object* v_openDecls_1088_; lean_object* v_initHeartbeats_1089_; lean_object* v_maxHeartbeats_1090_; lean_object* v_quotContext_1091_; lean_object* v_currMacroScope_1092_; uint8_t v_diag_1093_; lean_object* v_cancelTk_x3f_1094_; uint8_t v_suppressElabErrors_1095_; lean_object* v_inheritedTraceOptions_1096_; lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_fileName_1081_ = lean_ctor_get(v___y_1078_, 0);
v_fileMap_1082_ = lean_ctor_get(v___y_1078_, 1);
v_options_1083_ = lean_ctor_get(v___y_1078_, 2);
v_currRecDepth_1084_ = lean_ctor_get(v___y_1078_, 3);
v_maxRecDepth_1085_ = lean_ctor_get(v___y_1078_, 4);
v_ref_1086_ = lean_ctor_get(v___y_1078_, 5);
v_currNamespace_1087_ = lean_ctor_get(v___y_1078_, 6);
v_openDecls_1088_ = lean_ctor_get(v___y_1078_, 7);
v_initHeartbeats_1089_ = lean_ctor_get(v___y_1078_, 8);
v_maxHeartbeats_1090_ = lean_ctor_get(v___y_1078_, 9);
v_quotContext_1091_ = lean_ctor_get(v___y_1078_, 10);
v_currMacroScope_1092_ = lean_ctor_get(v___y_1078_, 11);
v_diag_1093_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*14);
v_cancelTk_x3f_1094_ = lean_ctor_get(v___y_1078_, 12);
v_suppressElabErrors_1095_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1096_ = lean_ctor_get(v___y_1078_, 13);
v_ref_1097_ = l_Lean_replaceRef(v_ref_1076_, v_ref_1086_);
lean_inc_ref(v_inheritedTraceOptions_1096_);
lean_inc(v_cancelTk_x3f_1094_);
lean_inc(v_currMacroScope_1092_);
lean_inc(v_quotContext_1091_);
lean_inc(v_maxHeartbeats_1090_);
lean_inc(v_initHeartbeats_1089_);
lean_inc(v_openDecls_1088_);
lean_inc(v_currNamespace_1087_);
lean_inc(v_maxRecDepth_1085_);
lean_inc(v_currRecDepth_1084_);
lean_inc_ref(v_options_1083_);
lean_inc_ref(v_fileMap_1082_);
lean_inc_ref(v_fileName_1081_);
v___x_1098_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1098_, 0, v_fileName_1081_);
lean_ctor_set(v___x_1098_, 1, v_fileMap_1082_);
lean_ctor_set(v___x_1098_, 2, v_options_1083_);
lean_ctor_set(v___x_1098_, 3, v_currRecDepth_1084_);
lean_ctor_set(v___x_1098_, 4, v_maxRecDepth_1085_);
lean_ctor_set(v___x_1098_, 5, v_ref_1097_);
lean_ctor_set(v___x_1098_, 6, v_currNamespace_1087_);
lean_ctor_set(v___x_1098_, 7, v_openDecls_1088_);
lean_ctor_set(v___x_1098_, 8, v_initHeartbeats_1089_);
lean_ctor_set(v___x_1098_, 9, v_maxHeartbeats_1090_);
lean_ctor_set(v___x_1098_, 10, v_quotContext_1091_);
lean_ctor_set(v___x_1098_, 11, v_currMacroScope_1092_);
lean_ctor_set(v___x_1098_, 12, v_cancelTk_x3f_1094_);
lean_ctor_set(v___x_1098_, 13, v_inheritedTraceOptions_1096_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*14, v_diag_1093_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*14 + 1, v_suppressElabErrors_1095_);
v___x_1099_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1077_, v___x_1098_, v___y_1079_);
lean_dec_ref_known(v___x_1098_, 14);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1100_, v_msg_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v_ref_1100_);
return v_res_1105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1127_, lean_object* v_declHint_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_env_1132_; uint8_t v___x_1133_; 
v___x_1131_ = lean_st_ref_get(v___y_1129_);
v_env_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_env_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_Name_isAnonymous(v_declHint_1128_);
if (v___x_1133_ == 0)
{
uint8_t v_isExporting_1134_; 
v_isExporting_1134_ = lean_ctor_get_uint8(v_env_1132_, sizeof(void*)*8);
if (v_isExporting_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_env_1132_);
lean_dec(v_declHint_1128_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1127_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
lean_inc_ref(v_env_1132_);
v___x_1136_ = l_Lean_Environment_setExporting(v_env_1132_, v___x_1133_);
lean_inc(v_declHint_1128_);
lean_inc_ref(v___x_1136_);
v___x_1137_ = l_Lean_Environment_contains(v___x_1136_, v_declHint_1128_, v_isExporting_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_env_1132_);
lean_dec(v_declHint_1128_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_msg_1127_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_c_1144_; lean_object* v___x_1145_; 
v___x_1139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1141_ = l_Lean_Options_empty;
v___x_1142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1136_);
lean_ctor_set(v___x_1142_, 1, v___x_1139_);
lean_ctor_set(v___x_1142_, 2, v___x_1140_);
lean_ctor_set(v___x_1142_, 3, v___x_1141_);
lean_inc(v_declHint_1128_);
v___x_1143_ = l_Lean_MessageData_ofConstName(v_declHint_1128_, v___x_1133_);
v_c_1144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1144_, 0, v___x_1142_);
lean_ctor_set(v_c_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1132_, v_declHint_1128_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_env_1132_);
lean_dec(v_declHint_1128_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_c_1144_);
v___x_1148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_note(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_msg_1127_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1188_; 
v_val_1153_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1155_ = v___x_1145_;
v_isShared_1156_ = v_isSharedCheck_1188_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_val_1153_);
lean_dec(v___x_1145_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1188_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_mod_1160_; uint8_t v___x_1161_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Lean_Environment_header(v_env_1132_);
lean_dec_ref(v_env_1132_);
v___x_1159_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1158_);
v_mod_1160_ = lean_array_get(v___x_1157_, v___x_1159_, v_val_1153_);
lean_dec(v_val_1153_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = l_Lean_isPrivateName(v_declHint_1128_);
lean_dec(v_declHint_1128_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_c_1144_);
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_MessageData_ofName(v_mod_1160_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_MessageData_note(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_msg_1127_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1171_);
v___x_1173_ = v___x_1155_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_c_1144_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_ofName(v_mod_1160_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_MessageData_note(v___x_1182_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_msg_1127_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1184_);
v___x_1186_ = v___x_1155_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1189_; 
lean_dec_ref(v_env_1132_);
lean_dec(v_declHint_1128_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_msg_1127_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1190_, lean_object* v_declHint_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1190_, v_declHint_1191_, v___y_1192_);
lean_dec(v___y_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1195_, lean_object* v_declHint_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v___x_1200_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1195_, v_declHint_1196_, v___y_1198_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1205_ = l_Lean_unknownIdentifierMessageTag;
v___x_1206_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_a_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1211_, lean_object* v_declHint_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1211_, v_declHint_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1217_, lean_object* v_msg_1218_, lean_object* v_declHint_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1218_, v_declHint_1219_, v___y_1220_, v___y_1221_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1217_, v_a_1224_, v___y_1220_, v___y_1221_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1226_, lean_object* v_msg_1227_, lean_object* v_declHint_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1226_, v_msg_1227_, v_declHint_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v_ref_1226_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1239_, lean_object* v_constName_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1245_ = 0;
lean_inc(v_constName_1240_);
v___x_1246_ = l_Lean_MessageData_ofConstName(v_constName_1240_, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1239_, v___x_1249_, v_constName_1240_, v___y_1241_, v___y_1242_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1251_, lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1251_, v_constName_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_ref_1251_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = l_List_reverse___redArg(v_a_1258_);
return v___x_1259_;
}
else
{
lean_object* v_head_1260_; lean_object* v_tail_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v_head_1260_ = lean_ctor_get(v_a_1257_, 0);
v_tail_1261_ = lean_ctor_get(v_a_1257_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1263_ = v_a_1257_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_tail_1261_);
lean_inc(v_head_1260_);
lean_dec(v_a_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_snd_1265_; uint8_t v___x_1266_; 
v_snd_1265_ = lean_ctor_get(v_head_1260_, 1);
v___x_1266_ = l_List_isEmpty___redArg(v_snd_1265_);
if (v___x_1266_ == 0)
{
lean_del_object(v___x_1263_);
lean_dec(v_head_1260_);
v_a_1257_ = v_tail_1261_;
goto _start;
}
else
{
lean_object* v___x_1269_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_a_1258_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_head_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_a_1258_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v_a_1257_ = v_tail_1261_;
v_a_1258_ = v___x_1269_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1273_, lean_object* v_cs_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_cs_1279_; uint8_t v___x_1283_; 
v___x_1278_ = lean_box(0);
v_cs_1279_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1274_, v___x_1278_);
v___x_1283_ = l_List_isEmpty___redArg(v_cs_1279_);
if (v___x_1283_ == 0)
{
lean_dec(v_n_1273_);
goto v___jp_1280_;
}
else
{
lean_object* v_ref_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_cs_1279_);
v_ref_1284_ = lean_ctor_get(v___y_1275_, 5);
v___x_1285_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1284_, v_n_1273_, v___y_1275_, v___y_1276_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
v___jp_1280_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1279_, v___x_1278_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1294_, lean_object* v_cs_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1294_, v_cs_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
lean_inc(v_n_1300_);
v___x_1304_ = l_Lean_realizeGlobalName(v_n_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1300_, v_a_1305_, v_a_1301_, v_a_1302_);
return v___x_1306_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_n_1300_);
v_a_1307_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1304_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1304_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_realizeGlobalConstCore(v_n_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1320_, lean_object* v_ref_1321_, lean_object* v_constName_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1321_, v_constName_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_ref_1328_, lean_object* v_constName_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1327_, v_ref_1328_, v_constName_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v_ref_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1334_, lean_object* v_ref_1335_, lean_object* v_msg_1336_, lean_object* v_declHint_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1335_, v_msg_1336_, v_declHint_1337_, v___y_1338_, v___y_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_ref_1343_, lean_object* v_msg_1344_, lean_object* v_declHint_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1342_, v_ref_1343_, v_msg_1344_, v_declHint_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v_ref_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1350_, lean_object* v_declHint_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1350_, v_declHint_1351_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1356_, lean_object* v_declHint_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1356_, v_declHint_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1362_, lean_object* v_ref_1363_, lean_object* v_msg_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1363_, v_msg_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_ref_1370_, lean_object* v_msg_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1369_, v_ref_1370_, v_msg_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v_ref_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1376_, lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1382_, v_msg_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
if (lean_obj_tag(v_a_1388_) == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = l_List_reverse___redArg(v_a_1389_);
return v___x_1390_;
}
else
{
lean_object* v_head_1391_; lean_object* v_tail_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1401_; 
v_head_1391_ = lean_ctor_get(v_a_1388_, 0);
v_tail_1392_ = lean_ctor_get(v_a_1388_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_a_1388_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1394_ = v_a_1388_;
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_tail_1392_);
lean_inc(v_head_1391_);
lean_dec(v_a_1388_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l_Lean_MessageData_ofExpr(v_head_1391_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_a_1389_);
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_a_1389_);
v___x_1398_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v_a_1388_ = v_tail_1392_;
v_a_1389_ = v___x_1398_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
if (lean_obj_tag(v_a_1402_) == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = l_List_reverse___redArg(v_a_1403_);
return v___x_1404_;
}
else
{
lean_object* v_head_1405_; lean_object* v_tail_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v_head_1405_ = lean_ctor_get(v_a_1402_, 0);
v_tail_1406_ = lean_ctor_get(v_a_1402_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_a_1402_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1408_ = v_a_1402_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_tail_1406_);
lean_inc(v_head_1405_);
lean_dec(v_a_1402_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = l_Lean_mkConst(v_head_1405_, v___x_1410_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_a_1403_);
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_a_1403_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v_a_1402_ = v_tail_1406_;
v_a_1403_ = v___x_1413_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1422_ = l_Lean_stringToMessageData(v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1423_, lean_object* v_cs_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
if (lean_obj_tag(v_cs_1424_) == 1)
{
lean_object* v_tail_1440_; 
v_tail_1440_ = lean_ctor_get(v_cs_1424_, 1);
if (lean_obj_tag(v_tail_1440_) == 0)
{
lean_object* v_head_1441_; lean_object* v___x_1442_; 
lean_dec(v_n_1423_);
v_head_1441_ = lean_ctor_get(v_cs_1424_, 0);
lean_inc(v_head_1441_);
lean_dec_ref_known(v_cs_1424_, 2);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_head_1441_);
return v___x_1442_;
}
else
{
goto v___jp_1428_;
}
}
else
{
goto v___jp_1428_;
}
v___jp_1428_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1429_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1430_ = l_Lean_MessageData_ofName(v_n_1423_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_box(0);
v___x_1435_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1424_, v___x_1434_);
v___x_1436_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1435_, v___x_1434_);
v___x_1437_ = l_Lean_MessageData_ofList(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1433_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1438_, v___y_1425_, v___y_1426_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1443_, lean_object* v_cs_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1443_, v_cs_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1453_; 
lean_inc(v_n_1449_);
v___x_1453_ = l_Lean_realizeGlobalConstCore(v_n_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1449_, v_a_1454_, v_a_1450_, v_a_1451_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_n_1449_);
v_a_1456_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1453_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1453_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_array_to_list(v_a_1470_);
return v___x_1471_;
}
else
{
lean_object* v_head_1472_; 
v_head_1472_ = lean_ctor_get(v_a_1469_, 0);
if (lean_obj_tag(v_head_1472_) == 1)
{
lean_object* v_fields_1473_; 
v_fields_1473_ = lean_ctor_get(v_head_1472_, 1);
if (lean_obj_tag(v_fields_1473_) == 0)
{
lean_object* v_tail_1474_; lean_object* v_n_1475_; lean_object* v___x_1476_; 
lean_inc_ref(v_head_1472_);
v_tail_1474_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_tail_1474_);
lean_dec_ref_known(v_a_1469_, 2);
v_n_1475_ = lean_ctor_get(v_head_1472_, 0);
lean_inc(v_n_1475_);
lean_dec_ref_known(v_head_1472_, 2);
v___x_1476_ = lean_array_push(v_a_1470_, v_n_1475_);
v_a_1469_ = v_tail_1474_;
v_a_1470_ = v___x_1476_;
goto _start;
}
else
{
lean_object* v_tail_1478_; 
v_tail_1478_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_tail_1478_);
lean_dec_ref_known(v_a_1469_, 2);
v_a_1469_ = v_tail_1478_;
goto _start;
}
}
else
{
lean_object* v_tail_1480_; 
v_tail_1480_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_tail_1480_);
lean_dec_ref_known(v_a_1469_, 2);
v_a_1469_ = v_tail_1480_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1488_ = l_Lean_MessageData_ofFormat(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1489_, lean_object* v_k_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
if (lean_obj_tag(v_stx_1489_) == 3)
{
lean_object* v_val_1494_; lean_object* v_preresolved_1495_; lean_object* v___x_1496_; lean_object* v_pre_1497_; uint8_t v___x_1498_; 
v_val_1494_ = lean_ctor_get(v_stx_1489_, 2);
lean_inc(v_val_1494_);
v_preresolved_1495_ = lean_ctor_get(v_stx_1489_, 3);
v___x_1496_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1495_);
v_pre_1497_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1495_, v___x_1496_);
v___x_1498_ = l_List_isEmpty___redArg(v_pre_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_val_1494_);
lean_dec_ref_known(v_stx_1489_, 4);
lean_dec_ref(v_k_1490_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_pre_1497_);
return v___x_1499_;
}
else
{
lean_object* v_fileName_1500_; lean_object* v_fileMap_1501_; lean_object* v_options_1502_; lean_object* v_currRecDepth_1503_; lean_object* v_maxRecDepth_1504_; lean_object* v_ref_1505_; lean_object* v_currNamespace_1506_; lean_object* v_openDecls_1507_; lean_object* v_initHeartbeats_1508_; lean_object* v_maxHeartbeats_1509_; lean_object* v_quotContext_1510_; lean_object* v_currMacroScope_1511_; uint8_t v_diag_1512_; lean_object* v_cancelTk_x3f_1513_; uint8_t v_suppressElabErrors_1514_; lean_object* v_inheritedTraceOptions_1515_; lean_object* v_ref_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v_pre_1497_);
v_fileName_1500_ = lean_ctor_get(v___y_1491_, 0);
v_fileMap_1501_ = lean_ctor_get(v___y_1491_, 1);
v_options_1502_ = lean_ctor_get(v___y_1491_, 2);
v_currRecDepth_1503_ = lean_ctor_get(v___y_1491_, 3);
v_maxRecDepth_1504_ = lean_ctor_get(v___y_1491_, 4);
v_ref_1505_ = lean_ctor_get(v___y_1491_, 5);
v_currNamespace_1506_ = lean_ctor_get(v___y_1491_, 6);
v_openDecls_1507_ = lean_ctor_get(v___y_1491_, 7);
v_initHeartbeats_1508_ = lean_ctor_get(v___y_1491_, 8);
v_maxHeartbeats_1509_ = lean_ctor_get(v___y_1491_, 9);
v_quotContext_1510_ = lean_ctor_get(v___y_1491_, 10);
v_currMacroScope_1511_ = lean_ctor_get(v___y_1491_, 11);
v_diag_1512_ = lean_ctor_get_uint8(v___y_1491_, sizeof(void*)*14);
v_cancelTk_x3f_1513_ = lean_ctor_get(v___y_1491_, 12);
v_suppressElabErrors_1514_ = lean_ctor_get_uint8(v___y_1491_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1515_ = lean_ctor_get(v___y_1491_, 13);
v_ref_1516_ = l_Lean_replaceRef(v_stx_1489_, v_ref_1505_);
lean_dec_ref_known(v_stx_1489_, 4);
lean_inc_ref(v_inheritedTraceOptions_1515_);
lean_inc(v_cancelTk_x3f_1513_);
lean_inc(v_currMacroScope_1511_);
lean_inc(v_quotContext_1510_);
lean_inc(v_maxHeartbeats_1509_);
lean_inc(v_initHeartbeats_1508_);
lean_inc(v_openDecls_1507_);
lean_inc(v_currNamespace_1506_);
lean_inc(v_maxRecDepth_1504_);
lean_inc(v_currRecDepth_1503_);
lean_inc_ref(v_options_1502_);
lean_inc_ref(v_fileMap_1501_);
lean_inc_ref(v_fileName_1500_);
v___x_1517_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1517_, 0, v_fileName_1500_);
lean_ctor_set(v___x_1517_, 1, v_fileMap_1501_);
lean_ctor_set(v___x_1517_, 2, v_options_1502_);
lean_ctor_set(v___x_1517_, 3, v_currRecDepth_1503_);
lean_ctor_set(v___x_1517_, 4, v_maxRecDepth_1504_);
lean_ctor_set(v___x_1517_, 5, v_ref_1516_);
lean_ctor_set(v___x_1517_, 6, v_currNamespace_1506_);
lean_ctor_set(v___x_1517_, 7, v_openDecls_1507_);
lean_ctor_set(v___x_1517_, 8, v_initHeartbeats_1508_);
lean_ctor_set(v___x_1517_, 9, v_maxHeartbeats_1509_);
lean_ctor_set(v___x_1517_, 10, v_quotContext_1510_);
lean_ctor_set(v___x_1517_, 11, v_currMacroScope_1511_);
lean_ctor_set(v___x_1517_, 12, v_cancelTk_x3f_1513_);
lean_ctor_set(v___x_1517_, 13, v_inheritedTraceOptions_1515_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*14, v_diag_1512_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*14 + 1, v_suppressElabErrors_1514_);
lean_inc(v___y_1492_);
v___x_1518_ = lean_apply_4(v_k_1490_, v_val_1494_, v___x_1517_, v___y_1492_, lean_box(0));
return v___x_1518_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_k_1490_);
v___x_1519_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1520_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1489_, v___x_1519_, v___y_1491_, v___y_1492_);
lean_dec(v_stx_1489_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1521_, lean_object* v_k_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1521_, v_k_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_fileName_1532_; lean_object* v_fileMap_1533_; lean_object* v_options_1534_; lean_object* v_currRecDepth_1535_; lean_object* v_maxRecDepth_1536_; lean_object* v_ref_1537_; lean_object* v_currNamespace_1538_; lean_object* v_openDecls_1539_; lean_object* v_initHeartbeats_1540_; lean_object* v_maxHeartbeats_1541_; lean_object* v_quotContext_1542_; lean_object* v_currMacroScope_1543_; uint8_t v_diag_1544_; lean_object* v_cancelTk_x3f_1545_; uint8_t v_suppressElabErrors_1546_; lean_object* v_inheritedTraceOptions_1547_; lean_object* v___x_1548_; lean_object* v_ref_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_fileName_1532_ = lean_ctor_get(v_a_1529_, 0);
v_fileMap_1533_ = lean_ctor_get(v_a_1529_, 1);
v_options_1534_ = lean_ctor_get(v_a_1529_, 2);
v_currRecDepth_1535_ = lean_ctor_get(v_a_1529_, 3);
v_maxRecDepth_1536_ = lean_ctor_get(v_a_1529_, 4);
v_ref_1537_ = lean_ctor_get(v_a_1529_, 5);
v_currNamespace_1538_ = lean_ctor_get(v_a_1529_, 6);
v_openDecls_1539_ = lean_ctor_get(v_a_1529_, 7);
v_initHeartbeats_1540_ = lean_ctor_get(v_a_1529_, 8);
v_maxHeartbeats_1541_ = lean_ctor_get(v_a_1529_, 9);
v_quotContext_1542_ = lean_ctor_get(v_a_1529_, 10);
v_currMacroScope_1543_ = lean_ctor_get(v_a_1529_, 11);
v_diag_1544_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*14);
v_cancelTk_x3f_1545_ = lean_ctor_get(v_a_1529_, 12);
v_suppressElabErrors_1546_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1547_ = lean_ctor_get(v_a_1529_, 13);
v___x_1548_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1549_ = l_Lean_replaceRef(v_stx_1528_, v_ref_1537_);
lean_inc_ref(v_inheritedTraceOptions_1547_);
lean_inc(v_cancelTk_x3f_1545_);
lean_inc(v_currMacroScope_1543_);
lean_inc(v_quotContext_1542_);
lean_inc(v_maxHeartbeats_1541_);
lean_inc(v_initHeartbeats_1540_);
lean_inc(v_openDecls_1539_);
lean_inc(v_currNamespace_1538_);
lean_inc(v_maxRecDepth_1536_);
lean_inc(v_currRecDepth_1535_);
lean_inc_ref(v_options_1534_);
lean_inc_ref(v_fileMap_1533_);
lean_inc_ref(v_fileName_1532_);
v___x_1550_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1550_, 0, v_fileName_1532_);
lean_ctor_set(v___x_1550_, 1, v_fileMap_1533_);
lean_ctor_set(v___x_1550_, 2, v_options_1534_);
lean_ctor_set(v___x_1550_, 3, v_currRecDepth_1535_);
lean_ctor_set(v___x_1550_, 4, v_maxRecDepth_1536_);
lean_ctor_set(v___x_1550_, 5, v_ref_1549_);
lean_ctor_set(v___x_1550_, 6, v_currNamespace_1538_);
lean_ctor_set(v___x_1550_, 7, v_openDecls_1539_);
lean_ctor_set(v___x_1550_, 8, v_initHeartbeats_1540_);
lean_ctor_set(v___x_1550_, 9, v_maxHeartbeats_1541_);
lean_ctor_set(v___x_1550_, 10, v_quotContext_1542_);
lean_ctor_set(v___x_1550_, 11, v_currMacroScope_1543_);
lean_ctor_set(v___x_1550_, 12, v_cancelTk_x3f_1545_);
lean_ctor_set(v___x_1550_, 13, v_inheritedTraceOptions_1547_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*14, v_diag_1544_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*14 + 1, v_suppressElabErrors_1546_);
v___x_1551_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1528_, v___x_1548_, v___x_1550_, v_a_1530_);
lean_dec_ref_known(v___x_1550_, 14);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_realizeGlobalConst(v_stx_1552_, v_a_1553_, v_a_1554_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
return v_res_1556_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_instMonadEIO(lean_box(0));
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_toApplicative_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1597_; 
v___x_1564_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1565_ = l_StateRefT_x27_instMonad___redArg(v___x_1564_);
v_toApplicative_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1565_, 1);
lean_dec(v_unused_1598_);
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1597_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_toApplicative_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1597_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_toFunctor_1570_; lean_object* v_toSeq_1571_; lean_object* v_toSeqLeft_1572_; lean_object* v_toSeqRight_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1595_; 
v_toFunctor_1570_ = lean_ctor_get(v_toApplicative_1566_, 0);
v_toSeq_1571_ = lean_ctor_get(v_toApplicative_1566_, 2);
v_toSeqLeft_1572_ = lean_ctor_get(v_toApplicative_1566_, 3);
v_toSeqRight_1573_ = lean_ctor_get(v_toApplicative_1566_, 4);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_toApplicative_1566_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_toApplicative_1566_, 1);
lean_dec(v_unused_1596_);
v___x_1575_ = v_toApplicative_1566_;
v_isShared_1576_ = v_isSharedCheck_1595_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_toSeqRight_1573_);
lean_inc(v_toSeqLeft_1572_);
lean_inc(v_toSeq_1571_);
lean_inc(v_toFunctor_1570_);
lean_dec(v_toApplicative_1566_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1595_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___f_1577_; lean_object* v___f_1578_; lean_object* v___f_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; lean_object* v___f_1584_; lean_object* v___x_1586_; 
v___f_1577_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1578_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1570_);
v___f_1579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1579_, 0, v_toFunctor_1570_);
v___f_1580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1580_, 0, v_toFunctor_1570_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___f_1579_);
lean_ctor_set(v___x_1581_, 1, v___f_1580_);
v___f_1582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1582_, 0, v_toSeqRight_1573_);
v___f_1583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1583_, 0, v_toSeqLeft_1572_);
v___f_1584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1584_, 0, v_toSeq_1571_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 4, v___f_1582_);
lean_ctor_set(v___x_1575_, 3, v___f_1583_);
lean_ctor_set(v___x_1575_, 2, v___f_1584_);
lean_ctor_set(v___x_1575_, 1, v___f_1577_);
lean_ctor_set(v___x_1575_, 0, v___x_1581_);
v___x_1586_ = v___x_1575_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___f_1577_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v___f_1584_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___f_1583_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v___f_1582_);
v___x_1586_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___f_1578_);
lean_ctor_set(v___x_1568_, 0, v___x_1586_);
v___x_1588_ = v___x_1568_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___f_1578_);
v___x_1588_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_195__overap_1591_; lean_object* v___x_1592_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = l_instInhabitedOfMonad___redArg(v___x_1588_, v___x_1589_);
v___x_195__overap_1591_ = lean_panic_fn_borrowed(v___x_1590_, v_msg_1560_);
lean_dec(v___x_1590_);
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
v___x_1592_ = lean_apply_3(v___x_195__overap_1591_, v___y_1561_, v___y_1562_, lean_box(0));
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
if (lean_obj_tag(v_x_1606_) == 0)
{
return v_x_1605_;
}
else
{
lean_object* v_head_1607_; lean_object* v_tail_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_head_1607_ = lean_ctor_get(v_x_1606_, 0);
v_tail_1608_ = lean_ctor_get(v_x_1606_, 1);
v___x_1609_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1610_ = lean_string_append(v_x_1605_, v___x_1609_);
v___x_1611_ = lean_expr_dbg_to_string(v_head_1607_);
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
lean_dec_ref(v___x_1611_);
v_x_1605_ = v___x_1612_;
v_x_1606_ = v_tail_1608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1614_, v_x_1615_);
lean_dec(v_x_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1621_;
}
else
{
lean_object* v_tail_1622_; 
v_tail_1622_ = lean_ctor_get(v_x_1620_, 1);
if (lean_obj_tag(v_tail_1622_) == 0)
{
lean_object* v_head_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_head_1623_ = lean_ctor_get(v_x_1620_, 0);
v___x_1624_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1625_ = lean_expr_dbg_to_string(v_head_1623_);
v___x_1626_ = lean_string_append(v___x_1624_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
return v___x_1628_;
}
else
{
lean_object* v_head_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint32_t v___x_1634_; lean_object* v___x_1635_; 
v_head_1629_ = lean_ctor_get(v_x_1620_, 0);
v___x_1630_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1631_ = lean_expr_dbg_to_string(v_head_1629_);
v___x_1632_ = lean_string_append(v___x_1630_, v___x_1631_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1632_, v_tail_1622_);
v___x_1634_ = 93;
v___x_1635_ = lean_string_push(v___x_1633_, v___x_1634_);
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1636_);
lean_dec(v_x_1636_);
return v_res_1637_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1642_ = lean_unsigned_to_nat(11u);
v___x_1643_ = lean_unsigned_to_nat(429u);
v___x_1644_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1645_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1646_ = l_mkPanicMessageWithDecl(v___x_1645_, v___x_1644_, v___x_1643_, v___x_1642_, v___x_1641_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1649_, lean_object* v_cs_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
if (lean_obj_tag(v_cs_1650_) == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_id_1649_);
v___x_1654_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1655_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1654_, v___y_1651_, v___y_1652_);
return v___x_1655_;
}
else
{
lean_object* v_tail_1656_; 
v_tail_1656_ = lean_ctor_get(v_cs_1650_, 1);
if (lean_obj_tag(v_tail_1656_) == 0)
{
lean_object* v_head_1657_; lean_object* v___x_1658_; 
lean_dec(v_id_1649_);
v_head_1657_ = lean_ctor_get(v_cs_1650_, 0);
lean_inc(v_head_1657_);
lean_dec_ref_known(v_cs_1650_, 2);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_head_1657_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1659_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1660_ = lean_box(0);
v___x_1661_ = 0;
lean_inc(v_id_1649_);
v___x_1662_ = l_Lean_Syntax_formatStx(v_id_1649_, v___x_1660_, v___x_1661_);
v___x_1663_ = l_Std_Format_defWidth;
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = l_Std_Format_pretty(v___x_1662_, v___x_1663_, v___x_1664_, v___x_1664_);
v___x_1666_ = lean_string_append(v___x_1659_, v___x_1665_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1668_ = lean_string_append(v___x_1666_, v___x_1667_);
v___x_1669_ = lean_box(0);
v___x_1670_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1650_, v___x_1669_);
v___x_1671_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1670_);
lean_dec(v___x_1670_);
v___x_1672_ = lean_string_append(v___x_1668_, v___x_1671_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
v___x_1675_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1649_, v___x_1674_, v___y_1651_, v___y_1652_);
lean_dec(v_id_1649_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1676_, lean_object* v_cs_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1676_, v_cs_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v_id_1682_);
v___x_1686_ = l_Lean_realizeGlobalConst(v_id_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1682_, v_a_1687_, v_a_1683_, v_a_1684_);
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_id_1682_);
v_a_1689_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1686_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1686_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_realizeGlobalConstNoOverload(v_id_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1701_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_unsigned_to_nat(3863082579u);
v___x_1734_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1735_ = l_Lean_Name_num___override(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1738_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1739_ = l_Lean_Name_str___override(v___x_1738_, v___x_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1742_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1743_ = l_Lean_Name_str___override(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_unsigned_to_nat(2u);
v___x_1745_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1746_ = l_Lean_Name_num___override(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1749_ = 0;
v___x_1750_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1751_ = l_Lean_registerTraceClass(v___x_1748_, v___x_1749_, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1753_;
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

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
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_toCold_184_; lean_object* v_currRecDepth_185_; lean_object* v_ref_186_; uint8_t v_diag_187_; uint8_t v_suppressElabErrors_188_; lean_object* v_ref_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_traceState_192_; lean_object* v_traces_193_; lean_object* v___x_194_; size_t v_sz_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v_msg_198_; lean_object* v___x_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_237_; 
v_toCold_184_ = lean_ctor_get(v___y_181_, 0);
v_currRecDepth_185_ = lean_ctor_get(v___y_181_, 1);
v_ref_186_ = lean_ctor_get(v___y_181_, 2);
v_diag_187_ = lean_ctor_get_uint8(v___y_181_, sizeof(void*)*3);
v_suppressElabErrors_188_ = lean_ctor_get_uint8(v___y_181_, sizeof(void*)*3 + 1);
v_ref_189_ = l_Lean_replaceRef(v_ref_179_, v_ref_186_);
lean_inc(v_currRecDepth_185_);
lean_inc_ref(v_toCold_184_);
v___x_190_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_190_, 0, v_toCold_184_);
lean_ctor_set(v___x_190_, 1, v_currRecDepth_185_);
lean_ctor_set(v___x_190_, 2, v_ref_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*3, v_diag_187_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*3 + 1, v_suppressElabErrors_188_);
v___x_191_ = lean_st_ref_get(v___y_182_);
v_traceState_192_ = lean_ctor_get(v___x_191_, 4);
lean_inc_ref(v_traceState_192_);
lean_dec(v___x_191_);
v_traces_193_ = lean_ctor_get(v_traceState_192_, 0);
lean_inc_ref(v_traces_193_);
lean_dec_ref(v_traceState_192_);
v___x_194_ = l_Lean_PersistentArray_toArray___redArg(v_traces_193_);
lean_dec_ref(v_traces_193_);
v_sz_195_ = lean_array_size(v___x_194_);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__4(v_sz_195_, v___x_196_, v___x_194_);
v_msg_198_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_198_, 0, v_data_178_);
lean_ctor_set(v_msg_198_, 1, v_msg_180_);
lean_ctor_set(v_msg_198_, 2, v___x_197_);
v___x_199_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_198_, v___x_190_, v___y_182_);
lean_dec_ref_known(v___x_190_, 3);
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
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_179_);
lean_ctor_set(v___x_222_, 1, v_a_200_);
v___x_223_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_177_, v___x_222_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_223_);
v___x_225_ = v___x_219_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_223_);
lean_ctor_set_uint64(v_reuseFailAlloc_233_, sizeof(void*)*1, v_tid_217_);
v___x_225_ = v_reuseFailAlloc_233_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 4, v___x_225_);
v___x_227_ = v___x_215_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_env_206_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_nextMacroScope_207_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_ngen_208_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_auxDeclNGen_209_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_cache_210_);
lean_ctor_set(v_reuseFailAlloc_232_, 6, v_messages_211_);
lean_ctor_set(v_reuseFailAlloc_232_, 7, v_infoState_212_);
lean_ctor_set(v_reuseFailAlloc_232_, 8, v_snapshotTasks_213_);
v___x_227_ = v_reuseFailAlloc_232_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_st_ref_put(v___y_182_, v___x_227_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_221_);
v___x_230_ = v___x_202_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_221_);
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
uint8_t v___x_399_; lean_object* v___x_5256__overap_400_; lean_object* v___x_401_; 
v___x_399_ = 1;
v___x_5256__overap_400_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
lean_inc(v___x_5256__overap_400_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc(v_name_391_);
v___x_401_ = lean_apply_4(v___x_5256__overap_400_, v_name_391_, v___y_395_, v___y_396_, lean_box(0));
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_414_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_414_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_414_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_414_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint8_t v___x_406_; 
v___x_406_ = lean_unbox(v_a_402_);
lean_dec(v_a_402_);
if (v___x_406_ == 0)
{
size_t v___x_407_; size_t v___x_408_; 
lean_del_object(v___x_404_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_393_, v___x_407_);
v_i_393_ = v___x_408_;
goto _start;
}
else
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v_name_391_);
v___x_410_ = lean_box(v___x_399_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_410_);
v___x_412_ = v___x_404_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
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
else
{
lean_dec(v_name_391_);
return v___x_401_;
}
}
else
{
uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v_name_391_);
v___x_415_ = 0;
v___x_416_ = lean_box(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(lean_object* v_name_418_, lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_stop_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v_i_boxed_425_ = lean_unbox_usize(v_i_420_);
lean_dec(v_i_420_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_421_);
lean_dec(v_stop_421_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_418_, v_as_419_, v_i_boxed_425_, v_stop_boxed_426_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_as_419_);
return v_res_427_;
}
}
static lean_object* _init_l_Lean_executeReservedNameAction___closed__5(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_436_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__4));
v___x_437_ = l_Lean_Name_append(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static double _init_l_Lean_executeReservedNameAction___closed__6(void){
_start:
{
lean_object* v___x_438_; double v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1000000000u);
v___x_439_ = lean_float_of_nat(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction(lean_object* v_name_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_toCold_444_; lean_object* v_options_445_; lean_object* v_inheritedTraceOptions_446_; uint8_t v_hasTrace_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___y_451_; 
v_toCold_444_ = lean_ctor_get(v_a_441_, 0);
v_options_445_ = lean_ctor_get(v_toCold_444_, 2);
v_inheritedTraceOptions_446_ = lean_ctor_get(v_toCold_444_, 11);
v_hasTrace_447_ = lean_ctor_get_uint8(v_options_445_, sizeof(void*)*1);
v___x_448_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
v___x_449_ = lean_box(0);
if (v_hasTrace_447_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_st_ref_get(v___x_448_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v___x_468_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v___x_468_);
lean_dec(v_name_440_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_449_);
return v___x_472_;
}
else
{
if (v___x_471_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v___x_468_);
lean_dec(v_name_440_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_449_);
return v___x_473_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_470_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_440_, v___x_468_, v___x_474_, v___x_475_, v_a_441_, v_a_442_);
lean_dec(v___x_468_);
v___y_451_ = v___x_476_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v_a_485_; lean_object* v___y_498_; lean_object* v___y_499_; uint8_t v_a_500_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v_a_506_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v_a_518_; 
lean_inc(v_name_440_);
v___f_477_ = lean_alloc_closure((void*)(l_Lean_executeReservedNameAction___lam__0___boxed), 5, 1);
lean_closure_set(v___f_477_, 0, v_name_440_);
v___x_478_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_479_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
v___x_480_ = lean_obj_once(&l_Lean_executeReservedNameAction___closed__5, &l_Lean_executeReservedNameAction___closed__5_once, _init_l_Lean_executeReservedNameAction___closed__5);
v___x_481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_446_, v_options_445_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = l_Lean_trace_profiler;
v___x_563_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_445_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec_ref(v___f_477_);
v___x_564_ = lean_st_ref_get(v___x_448_);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_array_get_size(v___x_564_);
v___x_567_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v___x_564_);
lean_dec(v_name_440_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_449_);
return v___x_568_;
}
else
{
if (v___x_567_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_564_);
lean_dec(v_name_440_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_449_);
return v___x_569_;
}
else
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_566_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_440_, v___x_564_, v___x_570_, v___x_571_, v_a_441_, v_a_442_);
lean_dec(v___x_564_);
v___y_451_ = v___x_572_;
goto v___jp_450_;
}
}
}
else
{
goto v___jp_521_;
}
}
else
{
goto v___jp_521_;
}
v___jp_482_:
{
lean_object* v___x_486_; double v___x_487_; double v___x_488_; double v___x_489_; double v___x_490_; double v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_486_ = lean_io_mono_nanos_now();
v___x_487_ = lean_float_of_nat(v___y_484_);
v___x_488_ = lean_float_once(&l_Lean_executeReservedNameAction___closed__6, &l_Lean_executeReservedNameAction___closed__6_once, _init_l_Lean_executeReservedNameAction___closed__6);
v___x_489_ = lean_float_div(v___x_487_, v___x_488_);
v___x_490_ = lean_float_of_nat(v___x_486_);
v___x_491_ = lean_float_div(v___x_490_, v___x_488_);
v___x_492_ = lean_box_float(v___x_489_);
v___x_493_ = lean_box_float(v___x_491_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_a_485_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_478_, v_hasTrace_447_, v___x_479_, v_options_445_, v___x_481_, v___y_483_, v___f_477_, v___x_495_, v_a_441_, v_a_442_);
v___y_451_ = v___x_496_;
goto v___jp_450_;
}
v___jp_497_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(v_a_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___y_483_ = v___y_499_;
v___y_484_ = v___y_498_;
v_a_485_ = v___x_502_;
goto v___jp_482_;
}
v___jp_503_:
{
lean_object* v___x_507_; double v___x_508_; double v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_507_ = lean_io_get_num_heartbeats();
v___x_508_ = lean_float_of_nat(v___y_504_);
v___x_509_ = lean_float_of_nat(v___x_507_);
v___x_510_ = lean_box_float(v___x_508_);
v___x_511_ = lean_box_float(v___x_509_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_a_506_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_478_, v_hasTrace_447_, v___x_479_, v_options_445_, v___x_481_, v___y_505_, v___f_477_, v___x_513_, v_a_441_, v_a_442_);
v___y_451_ = v___x_514_;
goto v___jp_450_;
}
v___jp_515_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(v_a_518_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___y_504_ = v___y_516_;
v___y_505_ = v___y_517_;
v_a_506_ = v___x_520_;
goto v___jp_503_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_442_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_trace_profiler_useHeartbeats;
v___x_525_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_445_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_526_ = lean_io_mono_nanos_now();
v___x_527_ = lean_st_ref_get(v___x_448_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_array_get_size(v___x_527_);
v___x_530_ = lean_nat_dec_lt(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v___x_527_);
lean_dec(v_name_440_);
v___y_498_ = v___x_526_;
v___y_499_ = v_a_523_;
v_a_500_ = v___x_530_;
goto v___jp_497_;
}
else
{
if (v___x_530_ == 0)
{
lean_dec(v___x_527_);
lean_dec(v_name_440_);
v___y_498_ = v___x_526_;
v___y_499_ = v_a_523_;
v_a_500_ = v___x_530_;
goto v___jp_497_;
}
else
{
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((size_t)0ULL);
v___x_532_ = lean_usize_of_nat(v___x_529_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_440_, v___x_527_, v___x_531_, v___x_532_, v_a_441_, v_a_442_);
lean_dec(v___x_527_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_unbox(v_a_534_);
lean_dec(v_a_534_);
v___y_498_ = v___x_526_;
v___y_499_ = v_a_523_;
v_a_500_ = v___x_535_;
goto v___jp_497_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_533_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_533_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 0);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v___y_483_ = v_a_523_;
v___y_484_ = v___x_526_;
v_a_485_ = v___x_541_;
goto v___jp_482_;
}
}
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_544_ = lean_io_get_num_heartbeats();
v___x_545_ = lean_st_ref_get(v___x_448_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_array_get_size(v___x_545_);
v___x_548_ = lean_nat_dec_lt(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v___x_545_);
lean_dec(v_name_440_);
v___y_516_ = v___x_544_;
v___y_517_ = v_a_523_;
v_a_518_ = v___x_548_;
goto v___jp_515_;
}
else
{
if (v___x_548_ == 0)
{
lean_dec(v___x_545_);
lean_dec(v_name_440_);
v___y_516_ = v___x_544_;
v___y_517_ = v_a_523_;
v_a_518_ = v___x_548_;
goto v___jp_515_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_547_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_440_, v___x_545_, v___x_549_, v___x_550_, v_a_441_, v_a_442_);
lean_dec(v___x_545_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; uint8_t v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
v___y_516_ = v___x_544_;
v___y_517_ = v_a_523_;
v_a_518_ = v___x_553_;
goto v___jp_515_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_551_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_551_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v___y_504_ = v___x_544_;
v___y_505_ = v_a_523_;
v_a_506_ = v___x_559_;
goto v___jp_503_;
}
}
}
}
}
}
}
}
v___jp_450_:
{
if (lean_obj_tag(v___y_451_) == 0)
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_isSharedCheck_458_ = !lean_is_exclusive(v___y_451_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___y_451_, 0);
lean_dec(v_unused_459_);
v___x_453_ = v___y_451_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_dec(v___y_451_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_449_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_449_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_a_460_ = lean_ctor_get(v___y_451_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___y_451_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___y_451_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___y_451_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_executeReservedNameAction___boxed(lean_object* v_name_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_executeReservedNameAction(v_name_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(lean_object* v_00_u03b1_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___redArg(v_x_579_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(lean_object* v_00_u03b1_584_, lean_object* v_x_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_00_u03b1_584_, v_x_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_597_, uint8_t v___y_598_, lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 1)
{
lean_object* v_pre_600_; 
v_pre_600_ = lean_ctor_get(v_x_599_, 0);
switch(lean_obj_tag(v_pre_600_))
{
case 1:
{
lean_object* v_pre_601_; 
v_pre_601_ = lean_ctor_get(v_pre_600_, 0);
switch(lean_obj_tag(v_pre_601_))
{
case 0:
{
lean_object* v_str_602_; lean_object* v_str_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_str_602_ = lean_ctor_get(v_x_599_, 1);
v_str_603_ = lean_ctor_get(v_pre_600_, 1);
v___x_604_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_605_ = lean_string_dec_eq(v_str_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_607_ = lean_string_dec_eq(v_str_603_, v___x_606_);
if (v___x_607_ == 0)
{
return v___x_607_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_609_ = lean_string_dec_eq(v_str_602_, v___x_608_);
if (v___x_609_ == 0)
{
return v___x_609_;
}
else
{
return v_suppressElabErrors_597_;
}
}
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_611_ = lean_string_dec_eq(v_str_602_, v___x_610_);
if (v___x_611_ == 0)
{
return v___x_611_;
}
else
{
return v_suppressElabErrors_597_;
}
}
}
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_pre_601_, 0);
if (lean_obj_tag(v_pre_612_) == 0)
{
lean_object* v_str_613_; lean_object* v_str_614_; lean_object* v_str_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_str_613_ = lean_ctor_get(v_x_599_, 1);
v_str_614_ = lean_ctor_get(v_pre_600_, 1);
v_str_615_ = lean_ctor_get(v_pre_601_, 1);
v___x_616_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_617_ = lean_string_dec_eq(v_str_615_, v___x_616_);
if (v___x_617_ == 0)
{
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_619_ = lean_string_dec_eq(v_str_614_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_621_ = lean_string_dec_eq(v_str_613_, v___x_620_);
if (v___x_621_ == 0)
{
return v___x_621_;
}
else
{
return v_suppressElabErrors_597_;
}
}
}
}
else
{
return v___y_598_;
}
}
default: 
{
return v___y_598_;
}
}
}
case 0:
{
lean_object* v_str_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_str_622_ = lean_ctor_get(v_x_599_, 1);
v___x_623_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__3));
v___x_624_ = lean_string_dec_eq(v_str_622_, v___x_623_);
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
return v_suppressElabErrors_597_;
}
}
default: 
{
return v___y_598_;
}
}
}
else
{
return v___y_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_625_, lean_object* v___y_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_suppressElabErrors_boxed_628_; uint8_t v___y_4860__boxed_629_; uint8_t v_res_630_; lean_object* v_r_631_; 
v_suppressElabErrors_boxed_628_ = lean_unbox(v_suppressElabErrors_625_);
v___y_4860__boxed_629_ = lean_unbox(v___y_626_);
v_res_630_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_628_, v___y_4860__boxed_629_, v_x_627_);
lean_dec(v_x_627_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(lean_object* v_ref_632_, lean_object* v_msgData_633_, uint8_t v_severity_634_, uint8_t v_isSilent_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v_currNamespace_647_; lean_object* v_openDecls_648_; lean_object* v___y_649_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; uint8_t v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; uint8_t v___x_728_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; uint8_t v___y_735_; uint8_t v___y_736_; lean_object* v___y_737_; uint8_t v___y_738_; uint8_t v___y_740_; uint8_t v___x_758_; 
v___x_728_ = 2;
v___x_758_ = l_Lean_instBEqMessageSeverity_beq(v_severity_634_, v___x_728_);
if (v___x_758_ == 0)
{
v___y_740_ = v___x_758_;
goto v___jp_739_;
}
else
{
uint8_t v___x_759_; 
lean_inc_ref(v_msgData_633_);
v___x_759_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_633_);
v___y_740_ = v___x_759_;
goto v___jp_739_;
}
v___jp_639_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_env_654_; lean_object* v_nextMacroScope_655_; lean_object* v_ngen_656_; lean_object* v_auxDeclNGen_657_; lean_object* v_traceState_658_; lean_object* v_cache_659_; lean_object* v_messages_660_; lean_object* v_infoState_661_; lean_object* v_snapshotTasks_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_673_; 
lean_inc(v_openDecls_648_);
lean_inc(v_currNamespace_647_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_currNamespace_647_);
lean_ctor_set(v___x_650_, 1, v_openDecls_648_);
v___x_651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_644_);
lean_inc_ref(v___y_645_);
lean_inc_ref(v___y_641_);
v___x_652_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_652_, 0, v___y_641_);
lean_ctor_set(v___x_652_, 1, v___y_646_);
lean_ctor_set(v___x_652_, 2, v___y_643_);
lean_ctor_set(v___x_652_, 3, v___y_645_);
lean_ctor_set(v___x_652_, 4, v___x_651_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*5, v___y_640_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*5 + 1, v___y_642_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*5 + 2, v_isSilent_635_);
v___x_653_ = lean_st_ref_take(v___y_649_);
v_env_654_ = lean_ctor_get(v___x_653_, 0);
v_nextMacroScope_655_ = lean_ctor_get(v___x_653_, 1);
v_ngen_656_ = lean_ctor_get(v___x_653_, 2);
v_auxDeclNGen_657_ = lean_ctor_get(v___x_653_, 3);
v_traceState_658_ = lean_ctor_get(v___x_653_, 4);
v_cache_659_ = lean_ctor_get(v___x_653_, 5);
v_messages_660_ = lean_ctor_get(v___x_653_, 6);
v_infoState_661_ = lean_ctor_get(v___x_653_, 7);
v_snapshotTasks_662_ = lean_ctor_get(v___x_653_, 8);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_673_ == 0)
{
v___x_664_ = v___x_653_;
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snapshotTasks_662_);
lean_inc(v_infoState_661_);
lean_inc(v_messages_660_);
lean_inc(v_cache_659_);
lean_inc(v_traceState_658_);
lean_inc(v_auxDeclNGen_657_);
lean_inc(v_ngen_656_);
lean_inc(v_nextMacroScope_655_);
lean_inc(v_env_654_);
lean_dec(v___x_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_MessageLog_add(v___x_652_, v_messages_660_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 6, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_env_654_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_nextMacroScope_655_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ngen_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_auxDeclNGen_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_traceState_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v_cache_659_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_672_, 7, v_infoState_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 8, v_snapshotTasks_662_);
v___x_669_ = v_reuseFailAlloc_672_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_st_ref_put(v___y_649_, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_666_);
return v___x_671_;
}
}
}
v___jp_674_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_700_; 
v___x_685_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_633_);
v___x_686_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v___x_685_, v___y_636_, v___y_637_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_700_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_inc_ref_n(v___y_683_, 2);
v___x_691_ = l_Lean_FileMap_toPosition(v___y_683_, v___y_681_);
lean_dec(v___y_681_);
v___x_692_ = l_Lean_FileMap_toPosition(v___y_683_, v___y_684_);
lean_dec(v___y_684_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
v___x_694_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__2));
if (v___y_680_ == 0)
{
lean_del_object(v___x_689_);
lean_dec_ref(v___y_676_);
v___y_640_ = v___y_679_;
v___y_641_ = v___y_678_;
v___y_642_ = v___y_682_;
v___y_643_ = v___x_693_;
v___y_644_ = v_a_687_;
v___y_645_ = v___x_694_;
v___y_646_ = v___x_691_;
v_currNamespace_647_ = v___y_675_;
v_openDecls_648_ = v___y_677_;
v___y_649_ = v___y_637_;
goto v___jp_639_;
}
else
{
uint8_t v___x_695_; 
lean_inc(v_a_687_);
v___x_695_ = l_Lean_MessageData_hasTag(v___y_676_, v_a_687_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec_ref_known(v___x_693_, 1);
lean_dec_ref(v___x_691_);
lean_dec(v_a_687_);
v___x_696_ = lean_box(0);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_696_);
v___x_698_ = v___x_689_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_del_object(v___x_689_);
v___y_640_ = v___y_679_;
v___y_641_ = v___y_678_;
v___y_642_ = v___y_682_;
v___y_643_ = v___x_693_;
v___y_644_ = v_a_687_;
v___y_645_ = v___x_694_;
v___y_646_ = v___x_691_;
v_currNamespace_647_ = v___y_675_;
v_openDecls_648_ = v___y_677_;
v___y_649_ = v___y_637_;
goto v___jp_639_;
}
}
}
}
v___jp_701_:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Syntax_getTailPos_x3f(v___y_709_, v___y_705_);
lean_dec(v___y_709_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_inc(v___y_711_);
v___y_675_ = v___y_702_;
v___y_676_ = v___y_703_;
v___y_677_ = v___y_704_;
v___y_678_ = v___y_706_;
v___y_679_ = v___y_705_;
v___y_680_ = v___y_707_;
v___y_681_ = v___y_711_;
v___y_682_ = v___y_708_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_711_;
goto v___jp_674_;
}
else
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_712_, 1);
v___y_675_ = v___y_702_;
v___y_676_ = v___y_703_;
v___y_677_ = v___y_704_;
v___y_678_ = v___y_706_;
v___y_679_ = v___y_705_;
v___y_680_ = v___y_707_;
v___y_681_ = v___y_711_;
v___y_682_ = v___y_708_;
v___y_683_ = v___y_710_;
v___y_684_ = v_val_713_;
goto v___jp_674_;
}
}
v___jp_714_:
{
lean_object* v_ref_724_; lean_object* v___x_725_; 
v_ref_724_ = l_Lean_replaceRef(v_ref_632_, v___y_722_);
v___x_725_ = l_Lean_Syntax_getPos_x3f(v_ref_724_, v___y_719_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___y_702_ = v___y_715_;
v___y_703_ = v___y_716_;
v___y_704_ = v___y_717_;
v___y_705_ = v___y_719_;
v___y_706_ = v___y_718_;
v___y_707_ = v___y_720_;
v___y_708_ = v___y_723_;
v___y_709_ = v_ref_724_;
v___y_710_ = v___y_721_;
v___y_711_ = v___x_726_;
goto v___jp_701_;
}
else
{
lean_object* v_val_727_; 
v_val_727_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_725_, 1);
v___y_702_ = v___y_715_;
v___y_703_ = v___y_716_;
v___y_704_ = v___y_717_;
v___y_705_ = v___y_719_;
v___y_706_ = v___y_718_;
v___y_707_ = v___y_720_;
v___y_708_ = v___y_723_;
v___y_709_ = v_ref_724_;
v___y_710_ = v___y_721_;
v___y_711_ = v_val_727_;
goto v___jp_701_;
}
}
v___jp_729_:
{
if (v___y_738_ == 0)
{
v___y_715_ = v___y_731_;
v___y_716_ = v___y_732_;
v___y_717_ = v___y_733_;
v___y_718_ = v___y_730_;
v___y_719_ = v___y_735_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_737_;
v___y_723_ = v_severity_634_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___y_731_;
v___y_716_ = v___y_732_;
v___y_717_ = v___y_733_;
v___y_718_ = v___y_730_;
v___y_719_ = v___y_735_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_737_;
v___y_723_ = v___x_728_;
goto v___jp_714_;
}
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
lean_object* v_toCold_741_; lean_object* v_ref_742_; uint8_t v_suppressElabErrors_743_; lean_object* v_fileName_744_; lean_object* v_fileMap_745_; lean_object* v_options_746_; lean_object* v_currNamespace_747_; lean_object* v_openDecls_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___f_751_; uint8_t v___x_752_; uint8_t v___x_753_; 
v_toCold_741_ = lean_ctor_get(v___y_636_, 0);
v_ref_742_ = lean_ctor_get(v___y_636_, 2);
v_suppressElabErrors_743_ = lean_ctor_get_uint8(v___y_636_, sizeof(void*)*3 + 1);
v_fileName_744_ = lean_ctor_get(v_toCold_741_, 0);
v_fileMap_745_ = lean_ctor_get(v_toCold_741_, 1);
v_options_746_ = lean_ctor_get(v_toCold_741_, 2);
v_currNamespace_747_ = lean_ctor_get(v_toCold_741_, 4);
v_openDecls_748_ = lean_ctor_get(v_toCold_741_, 5);
v___x_749_ = lean_box(v_suppressElabErrors_743_);
v___x_750_ = lean_box(v___y_740_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_751_, 0, v___x_749_);
lean_closure_set(v___f_751_, 1, v___x_750_);
v___x_752_ = 1;
v___x_753_ = l_Lean_instBEqMessageSeverity_beq(v_severity_634_, v___x_752_);
if (v___x_753_ == 0)
{
v___y_730_ = v_fileName_744_;
v___y_731_ = v_currNamespace_747_;
v___y_732_ = v___f_751_;
v___y_733_ = v_openDecls_748_;
v___y_734_ = v_fileMap_745_;
v___y_735_ = v___y_740_;
v___y_736_ = v_suppressElabErrors_743_;
v___y_737_ = v_ref_742_;
v___y_738_ = v___x_753_;
goto v___jp_729_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = l_Lean_warningAsError;
v___x_755_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_746_, v___x_754_);
v___y_730_ = v_fileName_744_;
v___y_731_ = v_currNamespace_747_;
v___y_732_ = v___f_751_;
v___y_733_ = v_openDecls_748_;
v___y_734_ = v_fileMap_745_;
v___y_735_ = v___y_740_;
v___y_736_ = v_suppressElabErrors_743_;
v___y_737_ = v_ref_742_;
v___y_738_ = v___x_755_;
goto v___jp_729_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v_msgData_633_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_760_, lean_object* v_msgData_761_, lean_object* v_severity_762_, lean_object* v_isSilent_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v_severity_boxed_767_; uint8_t v_isSilent_boxed_768_; lean_object* v_res_769_; 
v_severity_boxed_767_ = lean_unbox(v_severity_762_);
v_isSilent_boxed_768_ = lean_unbox(v_isSilent_763_);
v_res_769_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_760_, v_msgData_761_, v_severity_boxed_767_, v_isSilent_boxed_768_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v_ref_760_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(lean_object* v_msgData_770_, uint8_t v_severity_771_, uint8_t v_isSilent_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_ref_776_; lean_object* v___x_777_; 
v_ref_776_ = lean_ctor_get(v___y_773_, 2);
v___x_777_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_776_, v_msgData_770_, v_severity_771_, v_isSilent_772_, v___y_773_, v___y_774_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(lean_object* v_msgData_778_, lean_object* v_severity_779_, lean_object* v_isSilent_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_severity_boxed_784_; uint8_t v_isSilent_boxed_785_; lean_object* v_res_786_; 
v_severity_boxed_784_ = lean_unbox(v_severity_779_);
v_isSilent_boxed_785_ = lean_unbox(v_isSilent_780_);
v_res_786_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_778_, v_severity_boxed_784_, v_isSilent_boxed_785_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(lean_object* v_msgData_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = 2;
v___x_792_ = 0;
v___x_793_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_787_, v___x_791_, v___x_792_, v___y_788_, v___y_789_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(lean_object* v_msgData_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v_msgData_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_798_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(lean_object* v_id_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v_id_805_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_x_807_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_863_; 
v_head_812_ = lean_ctor_get(v_x_806_, 0);
v_tail_813_ = lean_ctor_get(v_x_806_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_806_);
if (v_isSharedCheck_863_ == 0)
{
v___x_815_ = v_x_806_;
v_isShared_816_ = v_isSharedCheck_863_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_head_812_);
lean_dec(v_x_806_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_863_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v_a_823_; lean_object* v_fst_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v_env_828_; uint8_t v___x_829_; 
v_fst_825_ = lean_ctor_get(v_head_812_, 0);
v___x_826_ = 1;
v___x_827_ = lean_st_ref_get(v___y_809_);
v_env_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_env_828_);
lean_dec(v___x_827_);
lean_inc(v_fst_825_);
v___x_829_ = l_Lean_Environment_contains(v_env_828_, v_fst_825_, v___x_826_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_inc(v_fst_825_);
v___x_830_ = l_Lean_executeReservedNameAction(v_fst_825_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; lean_object* v_env_832_; uint8_t v___x_833_; 
lean_dec_ref_known(v___x_830_, 1);
v___x_831_ = lean_st_ref_get(v___y_809_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = l_Lean_Environment_containsOnBranch(v_env_832_, v_fst_825_);
lean_dec_ref(v_env_832_);
v_a_823_ = v___x_833_;
goto v___jp_822_;
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_862_; 
v_a_834_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_862_ == 0)
{
v___x_836_ = v___x_830_;
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_830_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint8_t v___y_839_; uint8_t v___x_860_; 
v___x_860_ = l_Lean_Exception_isInterrupt(v_a_834_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
lean_inc(v_a_834_);
v___x_861_ = l_Lean_Exception_isRuntime(v_a_834_);
v___y_839_ = v___x_861_;
goto v___jp_838_;
}
else
{
v___y_839_ = v___x_860_;
goto v___jp_838_;
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_del_object(v___x_836_);
v___x_840_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
lean_inc(v_id_805_);
v___x_841_ = l_Lean_MessageData_ofName(v_id_805_);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_obj_once(&l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3, &l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once, _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_Exception_toMessageData(v_a_834_);
v___x_846_ = l_Lean_indentD(v___x_845_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_844_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(v___x_847_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_dec_ref_known(v___x_848_, 1);
v_a_823_ = v___x_829_;
goto v___jp_822_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_del_object(v___x_815_);
lean_dec(v_tail_813_);
lean_dec(v_head_812_);
lean_dec(v_x_807_);
lean_dec(v_id_805_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v___x_858_; 
lean_del_object(v___x_815_);
lean_dec(v_tail_813_);
lean_dec(v_head_812_);
lean_dec(v_x_807_);
lean_dec(v_id_805_);
if (v_isShared_837_ == 0)
{
v___x_858_ = v___x_836_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_834_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
else
{
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_819_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_x_807_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_head_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_x_807_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_x_806_ = v_tail_813_;
v_x_807_ = v___x_819_;
goto _start;
}
}
v___jp_822_:
{
if (v_a_823_ == 0)
{
lean_del_object(v___x_815_);
lean_dec(v_head_812_);
v_x_806_ = v_tail_813_;
goto _start;
}
else
{
goto v___jp_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(lean_object* v_id_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_864_, v_x_865_, v_x_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_box(0);
return v___x_872_;
}
else
{
lean_object* v_head_873_; lean_object* v_tail_874_; lean_object* v_fst_875_; uint8_t v___x_876_; 
v_head_873_ = lean_ctor_get(v_x_871_, 0);
v_tail_874_ = lean_ctor_get(v_x_871_, 1);
v_fst_875_ = lean_ctor_get(v_head_873_, 0);
v___x_876_ = l_Lean_isPrivateName(v_fst_875_);
if (v___x_876_ == 0)
{
v_x_871_ = v_tail_874_;
goto _start;
}
else
{
lean_object* v___x_878_; 
lean_inc(v_head_873_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_head_873_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_879_);
lean_dec(v_x_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(lean_object* v_msgData_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = 1;
v___x_886_ = 0;
v___x_887_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(v_msgData_881_, v___x_885_, v___x_886_, v___y_882_, v___y_883_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(lean_object* v_opt_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_toCold_896_; lean_object* v_options_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_toCold_896_ = lean_ctor_get(v___y_894_, 0);
v_options_897_ = lean_ctor_get(v_toCold_896_, 2);
v___x_898_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(v_options_897_, v_opt_893_);
v___x_899_ = lean_box(v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_opt_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_901_, v___y_902_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_opt_901_);
return v_res_904_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(lean_object* v_id_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v_env_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_938_; 
v___x_915_ = lean_st_ref_get(v___y_913_);
v_env_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_env_916_);
lean_dec(v___x_915_);
v___x_917_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_918_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_917_, v___y_912_);
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_938_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_938_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_938_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
uint8_t v_isExporting_928_; 
v_isExporting_928_ = lean_ctor_get_uint8(v_env_916_, sizeof(void*)*8);
lean_dec_ref(v_env_916_);
if (v_isExporting_928_ == 0)
{
lean_dec(v_a_919_);
lean_dec(v_id_911_);
goto v___jp_923_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_isPrivateName(v_id_911_);
if (v___x_929_ == 0)
{
lean_dec(v_a_919_);
lean_dec(v_id_911_);
goto v___jp_923_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
if (v___x_930_ == 0)
{
lean_dec(v_id_911_);
goto v___jp_923_;
}
else
{
lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_921_);
v___x_931_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
v___x_932_ = 0;
v___x_933_ = l_Lean_MessageData_ofConstName(v_id_911_, v___x_932_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_936_, v___y_912_, v___y_913_);
return v___x_937_;
}
}
}
v___jp_923_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_box(0);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
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
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(lean_object* v_id_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(lean_object* v_id_944_, uint8_t v_enableLog_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_toCold_950_; lean_object* v_env_951_; lean_object* v_options_952_; lean_object* v_currNamespace_953_; lean_object* v_openDecls_954_; lean_object* v_res_955_; lean_object* v___x_956_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_toCold_950_ = lean_ctor_get(v___y_946_, 0);
v_env_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_949_);
v_options_952_ = lean_ctor_get(v_toCold_950_, 2);
v_currNamespace_953_ = lean_ctor_get(v_toCold_950_, 4);
v_openDecls_954_ = lean_ctor_get(v_toCold_950_, 5);
lean_inc(v_openDecls_954_);
lean_inc(v_currNamespace_953_);
v_res_955_ = l_Lean_ResolveName_resolveGlobalName(v_env_951_, v_options_952_, v_currNamespace_953_, v_openDecls_954_, v_id_944_);
v___x_956_ = lean_st_ref_get(v___y_947_);
if (v_enableLog_945_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v___x_956_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v_res_955_);
return v___x_957_;
}
else
{
lean_object* v_env_958_; uint8_t v_isExporting_959_; 
v_env_958_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_956_);
v_isExporting_959_ = lean_ctor_get_uint8(v_env_958_, sizeof(void*)*8);
lean_dec_ref(v_env_958_);
if (v_isExporting_959_ == 0)
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_res_955_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_955_);
if (lean_obj_tag(v___x_961_) == 1)
{
lean_object* v_val_962_; lean_object* v_fst_963_; lean_object* v___x_964_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v___x_961_, 1);
v_fst_963_ = lean_ctor_get(v_val_962_, 0);
lean_inc(v_fst_963_);
lean_dec(v_val_962_);
v___x_964_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_963_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_964_, 0);
lean_dec(v_unused_972_);
v___x_966_ = v___x_964_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_dec(v___x_964_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_res_955_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_res_955_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_res_955_);
v_a_973_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_964_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_964_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_981_; 
lean_dec(v___x_961_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_res_955_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(lean_object* v_id_982_, lean_object* v_enableLog_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_enableLog_boxed_987_; lean_object* v_res_988_; 
v_enableLog_boxed_987_ = lean_unbox(v_enableLog_983_);
v_res_988_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_982_, v_enableLog_boxed_987_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName(lean_object* v_id_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
uint8_t v___x_993_; lean_object* v___x_994_; 
v___x_993_ = 1;
lean_inc(v_id_989_);
v___x_994_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(v_id_989_, v___x_993_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = lean_box(0);
v___x_997_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(v_id_989_, v_a_995_, v___x_996_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1006_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = l_List_reverse___redArg(v_a_998_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1002_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
return v___x_997_;
}
}
else
{
lean_dec(v_id_989_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalName___boxed(lean_object* v_id_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_realizeGlobalName(v_id_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(lean_object* v_opt_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_1012_, v___y_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(lean_object* v_opt_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_opt_1017_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
if (lean_obj_tag(v_a_1022_) == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = l_List_reverse___redArg(v_a_1023_);
return v___x_1024_;
}
else
{
lean_object* v_head_1025_; lean_object* v_tail_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1035_; 
v_head_1025_ = lean_ctor_get(v_a_1022_, 0);
v_tail_1026_ = lean_ctor_get(v_a_1022_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_1022_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1028_ = v_a_1022_;
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_tail_1026_);
lean_inc(v_head_1025_);
lean_dec(v_a_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_fst_1030_; lean_object* v___x_1032_; 
v_fst_1030_ = lean_ctor_get(v_head_1025_, 0);
lean_inc(v_fst_1030_);
lean_dec(v_head_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_a_1023_);
lean_ctor_set(v___x_1028_, 0, v_fst_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_fst_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1023_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v_a_1022_ = v_tail_1026_;
v_a_1023_ = v___x_1032_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_ref_1040_; lean_object* v___x_1041_; lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
v_ref_1040_ = lean_ctor_get(v___y_1037_, 2);
v___x_1041_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5(v_msg_1036_, v___y_1037_, v___y_1038_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_inc(v_ref_1040_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_ref_1040_);
lean_ctor_set(v___x_1046_, 1, v_a_1042_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 1);
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_toCold_1061_; lean_object* v_currRecDepth_1062_; lean_object* v_ref_1063_; uint8_t v_diag_1064_; uint8_t v_suppressElabErrors_1065_; lean_object* v_ref_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_toCold_1061_ = lean_ctor_get(v___y_1058_, 0);
v_currRecDepth_1062_ = lean_ctor_get(v___y_1058_, 1);
v_ref_1063_ = lean_ctor_get(v___y_1058_, 2);
v_diag_1064_ = lean_ctor_get_uint8(v___y_1058_, sizeof(void*)*3);
v_suppressElabErrors_1065_ = lean_ctor_get_uint8(v___y_1058_, sizeof(void*)*3 + 1);
v_ref_1066_ = l_Lean_replaceRef(v_ref_1056_, v_ref_1063_);
lean_inc(v_currRecDepth_1062_);
lean_inc_ref(v_toCold_1061_);
v___x_1067_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1067_, 0, v_toCold_1061_);
lean_ctor_set(v___x_1067_, 1, v_currRecDepth_1062_);
lean_ctor_set(v___x_1067_, 2, v_ref_1066_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*3, v_diag_1064_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*3 + 1, v_suppressElabErrors_1065_);
v___x_1068_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1057_, v___x_1067_, v___y_1059_);
lean_dec_ref_known(v___x_1067_, 3);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1069_, v_msg_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_ref_1069_);
return v_res_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_env_1102_; uint8_t v___x_1103_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_st_ref_get(v___y_1098_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = l_Lean_Name_isAnonymous(v_declHint_1097_);
if (v___x_1103_ == 0)
{
uint8_t v_isExporting_1104_; 
v_isExporting_1104_ = lean_ctor_get_uint8(v_env_1102_, sizeof(void*)*8);
if (v_isExporting_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_msg_1096_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
lean_inc_ref(v_env_1102_);
v___x_1106_ = l_Lean_Environment_setExporting(v_env_1102_, v___x_1103_);
lean_inc(v_declHint_1097_);
lean_inc_ref(v___x_1106_);
v___x_1107_ = l_Lean_Environment_contains(v___x_1106_, v_declHint_1097_, v_isExporting_1104_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_msg_1096_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_c_1114_; lean_object* v___x_1115_; 
v___x_1109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__2);
v___x_1110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3_spec__5___closed__5);
v___x_1111_ = l_Lean_Options_empty;
v___x_1112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1109_);
lean_ctor_set(v___x_1112_, 2, v___x_1110_);
lean_ctor_set(v___x_1112_, 3, v___x_1111_);
lean_inc(v_declHint_1097_);
v___x_1113_ = l_Lean_MessageData_ofConstName(v_declHint_1097_, v___x_1103_);
v_c_1114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1114_, 0, v___x_1112_);
lean_ctor_set(v_c_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1102_, v_declHint_1097_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_c_1114_);
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_note(v___x_1119_);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_msg_1096_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1157_; 
v_val_1123_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1125_ = v___x_1115_;
v_isShared_1126_ = v_isSharedCheck_1157_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v___x_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1157_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_mod_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l_Lean_Environment_header(v_env_1102_);
lean_dec_ref(v_env_1102_);
v___x_1128_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1127_);
v_mod_1129_ = lean_array_get(v___x_1100_, v___x_1128_, v_val_1123_);
lean_dec(v_val_1123_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_isPrivateName(v_declHint_1097_);
lean_dec(v_declHint_1097_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1114_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_note(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1096_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1140_);
v___x_1142_ = v___x_1125_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_c_1114_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_note(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1096_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1153_);
v___x_1155_ = v___x_1125_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msg_1096_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1159_, v_declHint_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1179_; 
v___x_1169_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1164_, v_declHint_1165_, v___y_1167_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = l_Lean_unknownIdentifierMessageTag;
v___x_1175_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_a_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1180_, lean_object* v_declHint_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1180_, v_declHint_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1186_, lean_object* v_msg_1187_, lean_object* v_declHint_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1194_; 
v___x_1192_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_1187_, v_declHint_1188_, v___y_1189_, v___y_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1186_, v_a_1193_, v___y_1189_, v___y_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1195_, lean_object* v_msg_1196_, lean_object* v_declHint_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1195_, v_msg_1196_, v_declHint_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v_ref_1195_);
return v_res_1201_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0));
v___x_1204_ = l_Lean_stringToMessageData(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(lean_object* v_ref_1208_, lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1213_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
v___x_1214_ = 0;
lean_inc(v_constName_1209_);
v___x_1215_ = l_Lean_MessageData_ofConstName(v_constName_1209_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1213_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1208_, v___x_1218_, v_constName_1209_, v___y_1210_, v___y_1211_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1220_, lean_object* v_constName_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1220_, v_constName_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v_ref_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = l_List_reverse___redArg(v_a_1227_);
return v___x_1228_;
}
else
{
lean_object* v_head_1229_; lean_object* v_tail_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1241_; 
v_head_1229_ = lean_ctor_get(v_a_1226_, 0);
v_tail_1230_ = lean_ctor_get(v_a_1226_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1232_ = v_a_1226_;
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_tail_1230_);
lean_inc(v_head_1229_);
lean_dec(v_a_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_snd_1234_; uint8_t v___x_1235_; 
v_snd_1234_ = lean_ctor_get(v_head_1229_, 1);
v___x_1235_ = l_List_isEmpty___redArg(v_snd_1234_);
if (v___x_1235_ == 0)
{
lean_del_object(v___x_1232_);
lean_dec(v_head_1229_);
v_a_1226_ = v_tail_1230_;
goto _start;
}
else
{
lean_object* v___x_1238_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_a_1227_);
v___x_1238_ = v___x_1232_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_head_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_a_1227_);
v___x_1238_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v_a_1226_ = v_tail_1230_;
v_a_1227_ = v___x_1238_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(lean_object* v_n_1242_, lean_object* v_cs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v_cs_1248_; uint8_t v___x_1252_; 
v___x_1247_ = lean_box(0);
v_cs_1248_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_1243_, v___x_1247_);
v___x_1252_ = l_List_isEmpty___redArg(v_cs_1248_);
if (v___x_1252_ == 0)
{
lean_dec(v_n_1242_);
goto v___jp_1249_;
}
else
{
lean_object* v_ref_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_cs_1248_);
v_ref_1253_ = lean_ctor_get(v___y_1244_, 2);
v___x_1254_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1253_, v_n_1242_, v___y_1244_, v___y_1245_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
v___jp_1249_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_1248_, v___x_1247_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(lean_object* v_n_1263_, lean_object* v_cs_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1263_, v_cs_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore(lean_object* v_n_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; 
lean_inc(v_n_1269_);
v___x_1273_ = l_Lean_realizeGlobalName(v_n_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(v_n_1269_, v_a_1274_, v_a_1270_, v_a_1271_);
return v___x_1275_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_n_1269_);
v_a_1276_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1273_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstCore___boxed(lean_object* v_n_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_realizeGlobalConstCore(v_n_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(lean_object* v_00_u03b1_1289_, lean_object* v_ref_1290_, lean_object* v_constName_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_1290_, v_constName_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_ref_1297_, lean_object* v_constName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_1296_, v_ref_1297_, v_constName_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v_ref_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1303_, lean_object* v_ref_1304_, lean_object* v_msg_1305_, lean_object* v_declHint_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_1304_, v_msg_1305_, v_declHint_1306_, v___y_1307_, v___y_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_ref_1312_, lean_object* v_msg_1313_, lean_object* v_declHint_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_1311_, v_ref_1312_, v_msg_1313_, v_declHint_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v_ref_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1319_, lean_object* v_declHint_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1319_, v_declHint_1320_, v___y_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1325_, lean_object* v_declHint_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1325_, v_declHint_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1331_, lean_object* v_ref_1332_, lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1332_, v_msg_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_ref_1339_, lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1338_, v_ref_1339_, v_msg_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v_ref_1339_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1345_, lean_object* v_msg_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1351_, v_msg_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
if (lean_obj_tag(v_a_1357_) == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = l_List_reverse___redArg(v_a_1358_);
return v___x_1359_;
}
else
{
lean_object* v_head_1360_; lean_object* v_tail_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_head_1360_ = lean_ctor_get(v_a_1357_, 0);
v_tail_1361_ = lean_ctor_get(v_a_1357_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1357_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1363_ = v_a_1357_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_tail_1361_);
lean_inc(v_head_1360_);
lean_dec(v_a_1357_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l_Lean_MessageData_ofExpr(v_head_1360_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_a_1358_);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1358_);
v___x_1367_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
v_a_1357_ = v_tail_1361_;
v_a_1358_ = v___x_1367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
if (lean_obj_tag(v_a_1371_) == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = l_List_reverse___redArg(v_a_1372_);
return v___x_1373_;
}
else
{
lean_object* v_head_1374_; lean_object* v_tail_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1385_; 
v_head_1374_ = lean_ctor_get(v_a_1371_, 0);
v_tail_1375_ = lean_ctor_get(v_a_1371_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_a_1371_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1377_ = v_a_1371_;
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_tail_1375_);
lean_inc(v_head_1374_);
lean_dec(v_a_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Lean_mkConst(v_head_1374_, v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v_a_1372_);
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_a_1372_);
v___x_1382_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
v_a_1371_ = v_tail_1375_;
v_a_1372_ = v___x_1382_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(lean_object* v_n_1392_, lean_object* v_cs_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_cs_1393_) == 1)
{
lean_object* v_tail_1409_; 
v_tail_1409_ = lean_ctor_get(v_cs_1393_, 1);
if (lean_obj_tag(v_tail_1409_) == 0)
{
lean_object* v_head_1410_; lean_object* v___x_1411_; 
lean_dec(v_n_1392_);
v_head_1410_ = lean_ctor_get(v_cs_1393_, 0);
lean_inc(v_head_1410_);
lean_dec_ref_known(v_cs_1393_, 2);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_head_1410_);
return v___x_1411_;
}
else
{
goto v___jp_1397_;
}
}
else
{
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1398_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
v___x_1399_ = l_Lean_MessageData_ofName(v_n_1392_);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = lean_obj_once(&l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3, &l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once, _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_box(0);
v___x_1404_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1393_, v___x_1403_);
v___x_1405_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_1404_, v___x_1403_);
v___x_1406_ = l_Lean_MessageData_ofList(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1402_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_1407_, v___y_1394_, v___y_1395_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(lean_object* v_n_1412_, lean_object* v_cs_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1412_, v_cs_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object* v_n_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; 
lean_inc(v_n_1418_);
v___x_1422_ = l_Lean_realizeGlobalConstCore(v_n_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_1418_, v_a_1423_, v_a_1419_, v_a_1420_);
return v___x_1424_;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_n_1418_);
v_a_1425_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1422_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverloadCore___boxed(lean_object* v_n_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
if (lean_obj_tag(v_a_1438_) == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_array_to_list(v_a_1439_);
return v___x_1440_;
}
else
{
lean_object* v_head_1441_; 
v_head_1441_ = lean_ctor_get(v_a_1438_, 0);
if (lean_obj_tag(v_head_1441_) == 1)
{
lean_object* v_fields_1442_; 
v_fields_1442_ = lean_ctor_get(v_head_1441_, 1);
if (lean_obj_tag(v_fields_1442_) == 0)
{
lean_object* v_tail_1443_; lean_object* v_n_1444_; lean_object* v___x_1445_; 
lean_inc_ref(v_head_1441_);
v_tail_1443_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_tail_1443_);
lean_dec_ref_known(v_a_1438_, 2);
v_n_1444_ = lean_ctor_get(v_head_1441_, 0);
lean_inc(v_n_1444_);
lean_dec_ref_known(v_head_1441_, 2);
v___x_1445_ = lean_array_push(v_a_1439_, v_n_1444_);
v_a_1438_ = v_tail_1443_;
v_a_1439_ = v___x_1445_;
goto _start;
}
else
{
lean_object* v_tail_1447_; 
v_tail_1447_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_tail_1447_);
lean_dec_ref_known(v_a_1438_, 2);
v_a_1438_ = v_tail_1447_;
goto _start;
}
}
else
{
lean_object* v_tail_1449_; 
v_tail_1449_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_tail_1449_);
lean_dec_ref_known(v_a_1438_, 2);
v_a_1438_ = v_tail_1449_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2));
v___x_1457_ = l_Lean_MessageData_ofFormat(v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(lean_object* v_stx_1458_, lean_object* v_k_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
if (lean_obj_tag(v_stx_1458_) == 3)
{
lean_object* v_val_1463_; lean_object* v_preresolved_1464_; lean_object* v___x_1465_; lean_object* v_pre_1466_; uint8_t v___x_1467_; 
v_val_1463_ = lean_ctor_get(v_stx_1458_, 2);
lean_inc(v_val_1463_);
v_preresolved_1464_ = lean_ctor_get(v_stx_1458_, 3);
v___x_1465_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0));
lean_inc(v_preresolved_1464_);
v_pre_1466_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_1464_, v___x_1465_);
v___x_1467_ = l_List_isEmpty___redArg(v_pre_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec_ref_known(v_stx_1458_, 4);
lean_dec(v_val_1463_);
lean_dec_ref(v_k_1459_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_pre_1466_);
return v___x_1468_;
}
else
{
lean_object* v_toCold_1469_; lean_object* v_currRecDepth_1470_; lean_object* v_ref_1471_; uint8_t v_diag_1472_; uint8_t v_suppressElabErrors_1473_; lean_object* v_ref_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec(v_pre_1466_);
v_toCold_1469_ = lean_ctor_get(v___y_1460_, 0);
v_currRecDepth_1470_ = lean_ctor_get(v___y_1460_, 1);
v_ref_1471_ = lean_ctor_get(v___y_1460_, 2);
v_diag_1472_ = lean_ctor_get_uint8(v___y_1460_, sizeof(void*)*3);
v_suppressElabErrors_1473_ = lean_ctor_get_uint8(v___y_1460_, sizeof(void*)*3 + 1);
v_ref_1474_ = l_Lean_replaceRef(v_stx_1458_, v_ref_1471_);
lean_dec_ref_known(v_stx_1458_, 4);
lean_inc(v_currRecDepth_1470_);
lean_inc_ref(v_toCold_1469_);
v___x_1475_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1475_, 0, v_toCold_1469_);
lean_ctor_set(v___x_1475_, 1, v_currRecDepth_1470_);
lean_ctor_set(v___x_1475_, 2, v_ref_1474_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*3, v_diag_1472_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*3 + 1, v_suppressElabErrors_1473_);
lean_inc(v___y_1461_);
v___x_1476_ = lean_apply_4(v_k_1459_, v_val_1463_, v___x_1475_, v___y_1461_, lean_box(0));
return v___x_1476_;
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v_k_1459_);
v___x_1477_ = lean_obj_once(&l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3, &l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once, _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
v___x_1478_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_1458_, v___x_1477_, v___y_1460_, v___y_1461_);
lean_dec(v_stx_1458_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(lean_object* v_stx_1479_, lean_object* v_k_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1479_, v_k_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst(lean_object* v_stx_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_toCold_1490_; lean_object* v_currRecDepth_1491_; lean_object* v_ref_1492_; uint8_t v_diag_1493_; uint8_t v_suppressElabErrors_1494_; lean_object* v___x_1495_; lean_object* v_ref_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_toCold_1490_ = lean_ctor_get(v_a_1487_, 0);
v_currRecDepth_1491_ = lean_ctor_get(v_a_1487_, 1);
v_ref_1492_ = lean_ctor_get(v_a_1487_, 2);
v_diag_1493_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*3);
v_suppressElabErrors_1494_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*3 + 1);
v___x_1495_ = ((lean_object*)(l_Lean_realizeGlobalConst___closed__0));
v_ref_1496_ = l_Lean_replaceRef(v_stx_1486_, v_ref_1492_);
lean_inc(v_currRecDepth_1491_);
lean_inc_ref(v_toCold_1490_);
v___x_1497_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1497_, 0, v_toCold_1490_);
lean_ctor_set(v___x_1497_, 1, v_currRecDepth_1491_);
lean_ctor_set(v___x_1497_, 2, v_ref_1496_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*3, v_diag_1493_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*3 + 1, v_suppressElabErrors_1494_);
v___x_1498_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(v_stx_1486_, v___x_1495_, v___x_1497_, v_a_1488_);
lean_dec_ref_known(v___x_1497_, 3);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConst___boxed(lean_object* v_stx_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_realizeGlobalConst(v_stx_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1503_;
}
}
static lean_object* _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_instMonadEIO___redArg();
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_toApplicative_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1544_; 
v___x_1511_ = lean_obj_once(&l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0, &l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
v___x_1512_ = l_StateRefT_x27_instMonad___redArg(v___x_1511_);
v_toApplicative_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1512_, 1);
lean_dec(v_unused_1545_);
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1544_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_toApplicative_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1544_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_toFunctor_1517_; lean_object* v_toSeq_1518_; lean_object* v_toSeqLeft_1519_; lean_object* v_toSeqRight_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1542_; 
v_toFunctor_1517_ = lean_ctor_get(v_toApplicative_1513_, 0);
v_toSeq_1518_ = lean_ctor_get(v_toApplicative_1513_, 2);
v_toSeqLeft_1519_ = lean_ctor_get(v_toApplicative_1513_, 3);
v_toSeqRight_1520_ = lean_ctor_get(v_toApplicative_1513_, 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_toApplicative_1513_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_toApplicative_1513_, 1);
lean_dec(v_unused_1543_);
v___x_1522_ = v_toApplicative_1513_;
v_isShared_1523_ = v_isSharedCheck_1542_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_toSeqRight_1520_);
lean_inc(v_toSeqLeft_1519_);
lean_inc(v_toSeq_1518_);
lean_inc(v_toFunctor_1517_);
lean_dec(v_toApplicative_1513_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1542_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___f_1531_; lean_object* v___x_1533_; 
v___f_1524_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1));
v___f_1525_ = ((lean_object*)(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1517_);
v___f_1526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1526_, 0, v_toFunctor_1517_);
v___f_1527_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1527_, 0, v_toFunctor_1517_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___f_1526_);
lean_ctor_set(v___x_1528_, 1, v___f_1527_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toSeqRight_1520_);
v___f_1530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1530_, 0, v_toSeqLeft_1519_);
v___f_1531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1531_, 0, v_toSeq_1518_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 4, v___f_1529_);
lean_ctor_set(v___x_1522_, 3, v___f_1530_);
lean_ctor_set(v___x_1522_, 2, v___f_1531_);
lean_ctor_set(v___x_1522_, 1, v___f_1524_);
lean_ctor_set(v___x_1522_, 0, v___x_1528_);
v___x_1533_ = v___x_1522_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___f_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v___f_1531_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v___f_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___f_1529_);
v___x_1533_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___f_1525_);
lean_ctor_set(v___x_1515_, 0, v___x_1533_);
v___x_1535_ = v___x_1515_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___f_1525_);
v___x_1535_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_195__overap_1538_; lean_object* v___x_1539_; 
v___x_1536_ = lean_box(0);
v___x_1537_ = l_instInhabitedOfMonad___redArg(v___x_1535_, v___x_1536_);
v___x_195__overap_1538_ = lean_panic_fn_borrowed(v___x_1537_, v_msg_1507_);
lean_dec(v___x_1537_);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
v___x_1539_ = lean_apply_3(v___x_195__overap_1538_, v___y_1508_, v___y_1509_, lean_box(0));
return v___x_1539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
if (lean_obj_tag(v_x_1553_) == 0)
{
return v_x_1552_;
}
else
{
lean_object* v_head_1554_; lean_object* v_tail_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_head_1554_ = lean_ctor_get(v_x_1553_, 0);
v_tail_1555_ = lean_ctor_get(v_x_1553_, 1);
v___x_1556_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0));
v___x_1557_ = lean_string_append(v_x_1552_, v___x_1556_);
v___x_1558_ = lean_expr_dbg_to_string(v_head_1554_);
v___x_1559_ = lean_string_append(v___x_1557_, v___x_1558_);
lean_dec_ref(v___x_1558_);
v_x_1552_ = v___x_1559_;
v_x_1553_ = v_tail_1555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_1561_, v_x_1562_);
lean_dec(v_x_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0));
return v___x_1568_;
}
else
{
lean_object* v_tail_1569_; 
v_tail_1569_ = lean_ctor_get(v_x_1567_, 1);
if (lean_obj_tag(v_tail_1569_) == 0)
{
lean_object* v_head_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_head_1570_ = lean_ctor_get(v_x_1567_, 0);
v___x_1571_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1572_ = lean_expr_dbg_to_string(v_head_1570_);
v___x_1573_ = lean_string_append(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2));
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
return v___x_1575_;
}
else
{
lean_object* v_head_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint32_t v___x_1581_; lean_object* v___x_1582_; 
v_head_1576_ = lean_ctor_get(v_x_1567_, 0);
v___x_1577_ = ((lean_object*)(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1));
v___x_1578_ = lean_expr_dbg_to_string(v_head_1576_);
v___x_1579_ = lean_string_append(v___x_1577_, v___x_1578_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_1579_, v_tail_1569_);
v___x_1581_ = 93;
v___x_1582_ = lean_string_push(v___x_1580_, v___x_1581_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(lean_object* v_x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_1583_);
lean_dec(v_x_1583_);
return v_res_1584_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1588_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2));
v___x_1589_ = lean_unsigned_to_nat(11u);
v___x_1590_ = lean_unsigned_to_nat(429u);
v___x_1591_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1));
v___x_1592_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0));
v___x_1593_ = l_mkPanicMessageWithDecl(v___x_1592_, v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(lean_object* v_id_1596_, lean_object* v_cs_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
if (lean_obj_tag(v_cs_1597_) == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v_id_1596_);
v___x_1601_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3, &l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once, _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
v___x_1602_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_1601_, v___y_1598_, v___y_1599_);
return v___x_1602_;
}
else
{
lean_object* v_tail_1603_; 
v_tail_1603_ = lean_ctor_get(v_cs_1597_, 1);
if (lean_obj_tag(v_tail_1603_) == 0)
{
lean_object* v_head_1604_; lean_object* v___x_1605_; 
lean_dec(v_id_1596_);
v_head_1604_ = lean_ctor_get(v_cs_1597_, 0);
lean_inc(v_head_1604_);
lean_dec_ref_known(v_cs_1597_, 2);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_head_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1606_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4));
v___x_1607_ = lean_box(0);
v___x_1608_ = 0;
lean_inc(v_id_1596_);
v___x_1609_ = l_Lean_Syntax_formatStx(v_id_1596_, v___x_1607_, v___x_1608_);
v___x_1610_ = l_Std_Format_defWidth;
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = l_Std_Format_pretty(v___x_1609_, v___x_1610_, v___x_1611_, v___x_1611_);
v___x_1613_ = lean_string_append(v___x_1606_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5));
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
v___x_1616_ = lean_box(0);
v___x_1617_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_1597_, v___x_1616_);
v___x_1618_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_1617_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_string_append(v___x_1615_, v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofFormat(v___x_1620_);
v___x_1622_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_1596_, v___x_1621_, v___y_1598_, v___y_1599_);
lean_dec(v_id_1596_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(lean_object* v_id_1623_, lean_object* v_cs_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1623_, v_cs_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object* v_id_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; 
lean_inc(v_id_1629_);
v___x_1633_ = l_Lean_realizeGlobalConst(v_id_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_1629_, v_a_1634_, v_a_1630_, v_a_1631_);
return v___x_1635_;
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_id_1629_);
v_a_1636_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1633_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1633_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_realizeGlobalConstNoOverload___boxed(lean_object* v_id_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_realizeGlobalConstNoOverload(v_id_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1648_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_unsigned_to_nat(3863082579u);
v___x_1681_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1682_ = l_Lean_Name_num___override(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1685_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1686_ = l_Lean_Name_str___override(v___x_1685_, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_));
v___x_1689_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1690_ = l_Lean_Name_str___override(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_unsigned_to_nat(2u);
v___x_1692_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1693_ = l_Lean_Name_num___override(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = ((lean_object*)(l_Lean_executeReservedNameAction___closed__1));
v___x_1696_ = 0;
v___x_1697_ = lean_obj_once(&l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_, &l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once, _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
v___x_1698_ = l_Lean_registerTraceClass(v___x_1695_, v___x_1696_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
return v_res_1700_;
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

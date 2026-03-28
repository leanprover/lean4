// Lean compiler output
// Module: Lean.Language.Lean
// Imports: public import Lean.Language.Util public import Lean.Language.Lean.Types public import Lean.Elab.Import
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_IO_CancelToken_new();
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
extern lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
lean_object* lean_thunk_get_own(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Language_SnapshotTree_trace(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_;
extern lean_object* l_Lean_internal_cmdlineSnapshots;
lean_object* lean_mk_thunk(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
extern lean_object* l_Lean_Core_stderrAsMessages;
extern lean_object* l_ByteArray_empty;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_instInhabitedModuleParserState_default;
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshot_default;
lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object*);
lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_List_toPArray_x27___redArg(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler_output;
extern lean_object* l_Lean_instInhabitedTraceState_default;
lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO = (const lean_object*)&l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Language_Lean_isBeforeEditPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Language"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(175, 210, 78, 119, 167, 98, 198, 170)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 112, 34, 50, 214, 162, 204, 53)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(35, 57, 84, 103, 218, 237, 164, 234)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(110, 242, 18, 140, 130, 32, 167, 175)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(19, 205, 238, 85, 202, 45, 193, 251)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(126, 74, 26, 188, 17, 43, 130, 1)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "withHeaderExceptions"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 52, 36, 242, 101, 86, 247)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_Lean_setOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__0 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__0_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__1 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__1_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "invalid -D parameter, invalid configuration option '"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__2 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__2_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "' value, it must be true/false"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__3 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__3_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' value, it must be a natural number"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__4 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__4_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "invalid -D parameter, configuration option '"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__5 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__5_value;
static const lean_string_object l_Lean_Language_Lean_setOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "' cannot be set in the command line, use set_option command"};
static const lean_object* l_Lean_Language_Lean_setOption___closed__6 = (const lean_object*)&l_Lean_Language_Lean_setOption___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "weak"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 5, 49, 232, 223, 147, 119, 138)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "invalid -D parameter, unknown configuration option '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "'\n\nIf the option is defined in a library, use '-D"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' to set it conditionally"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "experimental"};
static const lean_object* l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 138, 38, 81, 136, 39, 83, 32)}};
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(93, 242, 21, 84, 145, 94, 84, 207)}};
static const lean_object* l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "no-op, deprecated"};
static const lean_object* l_Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 222, 85, 59, 197, 113, 89, 237)}};
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(24, 94, 31, 95, 17, 215, 109, 107)}};
static const lean_ctor_object l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 160, 244, 111, 154, 6, 107, 146)}};
static const lean_object* l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_experimental_module;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3_value;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "process"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 7, 72, 70, 238, 145, 97, 14)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElab"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(184, 73, 34, 28, 214, 248, 188, 54)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object**);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 108, 214, 181, 226, 69, 54, 12)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parseCmd"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snapshotTree"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 136, 72, 78, 187, 126, 217, 153)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object**);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 201, 190, 222, 246, 15, 232, 234)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1_value;
static const lean_array_object l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_import"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 157, 171, 65, 170, 18, 92, 252)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(12, 104, 192, 143, 94, 68, 237, 67)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "processHeader"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Import"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(36, 108, 229, 135, 237, 231, 134, 26)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "importing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parseHeader"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(152, 110, 119, 15, 255, 246, 245, 53)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(lean_object* v_00_u03b1_1_, lean_object* v_act_2_, lean_object* v_ctx_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_act_2_, v_ctx_3_, lean_box(0));
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_7_, lean_object* v_act_8_, lean_object* v_ctx_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(v_00_u03b1_7_, v_act_8_, v_ctx_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___lam__0(lean_object* v_00_u03b1_14_, lean_object* v_act_15_, lean_object* v_ctx_16_){
_start:
{
lean_object* v_toProcessingContext_17_; lean_object* v___x_18_; 
v_toProcessingContext_17_ = lean_ctor_get(v_ctx_16_, 0);
lean_inc_ref(v_toProcessingContext_17_);
lean_dec_ref(v_ctx_16_);
v___x_18_ = lean_apply_1(v_act_15_, v_toProcessingContext_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object* v_m_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = ((lean_object*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0));
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg(lean_object* v_act_22_, lean_object* v_oldInputCtx_x3f_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___y_27_; 
if (lean_obj_tag(v_oldInputCtx_x3f_23_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
v___y_27_ = v___x_30_;
goto v___jp_26_;
}
else
{
lean_object* v_val_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_41_; 
v_val_31_ = lean_ctor_get(v_oldInputCtx_x3f_23_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_oldInputCtx_x3f_23_);
if (v_isSharedCheck_41_ == 0)
{
v___x_33_ = v_oldInputCtx_x3f_23_;
v_isShared_34_ = v_isSharedCheck_41_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_val_31_);
lean_dec(v_oldInputCtx_x3f_23_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_41_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_inputString_35_; lean_object* v_inputString_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v_inputString_35_ = lean_ctor_get(v_val_31_, 0);
lean_inc_ref(v_inputString_35_);
lean_dec(v_val_31_);
v_inputString_36_ = lean_ctor_get(v_a_24_, 0);
v___x_37_ = l_String_firstDiffPos(v_inputString_35_, v_inputString_36_);
lean_dec_ref(v_inputString_35_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_37_);
v___x_39_ = v___x_33_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v___y_27_ = v___x_39_;
goto v___jp_26_;
}
}
}
v___jp_26_:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_inc_ref(v_a_24_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_a_24_);
lean_ctor_set(v___x_28_, 1, v___y_27_);
v___x_29_ = lean_apply_2(v_act_22_, v___x_28_, lean_box(0));
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg___boxed(lean_object* v_act_42_, lean_object* v_oldInputCtx_x3f_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_42_, v_oldInputCtx_x3f_43_, v_a_44_);
lean_dec_ref(v_a_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object* v_00_u03b1_47_, lean_object* v_act_48_, lean_object* v_oldInputCtx_x3f_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_48_, v_oldInputCtx_x3f_49_, v_a_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___boxed(lean_object* v_00_u03b1_53_, lean_object* v_act_54_, lean_object* v_oldInputCtx_x3f_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Language_Lean_LeanProcessingM_run(v_00_u03b1_53_, v_act_54_, v_oldInputCtx_x3f_55_, v_a_56_);
lean_dec_ref(v_a_56_);
return v_res_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_Lean_isBeforeEditPos(lean_object* v_pos_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_firstDiffPos_x3f_62_; 
v_firstDiffPos_x3f_62_ = lean_ctor_get(v_a_60_, 1);
if (lean_obj_tag(v_firstDiffPos_x3f_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
else
{
lean_object* v_val_64_; uint8_t v___x_65_; 
v_val_64_ = lean_ctor_get(v_firstDiffPos_x3f_62_, 0);
v___x_65_ = l_String_instDecidableLtRaw___aux__1(v_pos_59_, v_val_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object* v_pos_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_66_, v_a_67_);
lean_dec_ref(v_a_67_);
lean_dec(v_pos_66_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13(void){
_start:
{
uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = 1;
v___x_103_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12));
v___x_104_ = l_Lean_Name_toString(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(32u);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15(void){
_start:
{
size_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_108_ = ((size_t)5ULL);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_unsigned_to_nat(32u);
v___x_111_ = lean_mk_empty_array_with_capacity(v___x_110_);
v___x_112_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_113_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_109_);
lean_ctor_set(v___x_113_, 3, v___x_109_);
lean_ctor_set_usize(v___x_113_, 4, v___x_108_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16(void){
_start:
{
lean_object* v___x_114_; uint64_t v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15);
v___x_115_ = 0ULL;
v___x_116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint64(v___x_116_, sizeof(void*)*1, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(lean_object* v_ex_117_, lean_object* v_act_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
lean_inc_ref(v_a_119_);
v___x_121_ = lean_apply_2(v_act_118_, v_a_119_, lean_box(0));
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; 
lean_dec(v_ex_117_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
return v_a_122_;
}
else
{
lean_object* v_a_123_; lean_object* v_toProcessingContext_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v___x_121_);
v_toProcessingContext_124_ = lean_ctor_get(v_a_119_, 0);
v___x_125_ = lean_io_error_to_string(v_a_123_);
v___x_126_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_125_, v_toProcessingContext_124_);
v___x_127_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13);
v___x_128_ = lean_box(0);
v___x_129_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_131_, 0, v___x_127_);
lean_ctor_set(v___x_131_, 1, v___x_126_);
lean_ctor_set(v___x_131_, 2, v___x_128_);
lean_ctor_set(v___x_131_, 3, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*4, v___x_130_);
v___x_132_ = lean_apply_1(v_ex_117_, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(lean_object* v_ex_133_, lean_object* v_act_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_133_, v_act_134_, v_a_135_);
lean_dec_ref(v_a_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object* v_00_u03b1_138_, lean_object* v_ex_139_, lean_object* v_act_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_139_, v_act_140_, v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(lean_object* v_00_u03b1_144_, lean_object* v_ex_145_, lean_object* v_act_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(v_00_u03b1_144_, v_ex_145_, v_act_146_, v_a_147_);
lean_dec_ref(v_a_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(lean_object* v_o_153_, lean_object* v_k_154_, uint8_t v_v_155_){
_start:
{
lean_object* v_map_156_; uint8_t v_hasTrace_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_171_; 
v_map_156_ = lean_ctor_get(v_o_153_, 0);
v_hasTrace_157_ = lean_ctor_get_uint8(v_o_153_, sizeof(void*)*1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_o_153_);
if (v_isSharedCheck_171_ == 0)
{
v___x_159_ = v_o_153_;
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_map_156_);
lean_dec(v_o_153_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_161_, 0, v_v_155_);
lean_inc(v_k_154_);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_154_, v___x_161_, v_map_156_);
if (v_hasTrace_157_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_164_ = l_Lean_Name_isPrefixOf(v___x_163_, v_k_154_);
lean_dec(v_k_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_162_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_162_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_164_);
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
lean_dec(v_k_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_162_);
v___x_169_ = v___x_159_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*1, v_hasTrace_157_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(lean_object* v_o_172_, lean_object* v_k_173_, lean_object* v_v_174_){
_start:
{
uint8_t v_v_boxed_175_; lean_object* v_res_176_; 
v_v_boxed_175_ = lean_unbox(v_v_174_);
v_res_176_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_o_172_, v_k_173_, v_v_boxed_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(lean_object* v_o_177_, lean_object* v_k_178_, lean_object* v_v_179_){
_start:
{
lean_object* v_map_180_; uint8_t v_hasTrace_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_195_; 
v_map_180_ = lean_ctor_get(v_o_177_, 0);
v_hasTrace_181_ = lean_ctor_get_uint8(v_o_177_, sizeof(void*)*1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_o_177_);
if (v_isSharedCheck_195_ == 0)
{
v___x_183_ = v_o_177_;
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_map_180_);
lean_dec(v_o_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v_v_179_);
lean_inc(v_k_178_);
v___x_186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_178_, v___x_185_, v_map_180_);
if (v_hasTrace_181_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_190_; 
v___x_187_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_188_ = l_Lean_Name_isPrefixOf(v___x_187_, v_k_178_);
lean_dec(v_k_178_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_186_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_188_);
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec(v_k_178_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*1, v_hasTrace_181_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(lean_object* v_o_196_, lean_object* v_k_197_, lean_object* v_v_198_){
_start:
{
lean_object* v_map_199_; uint8_t v_hasTrace_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_214_; 
v_map_199_ = lean_ctor_get(v_o_196_, 0);
v_hasTrace_200_ = lean_ctor_get_uint8(v_o_196_, sizeof(void*)*1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_o_196_);
if (v_isSharedCheck_214_ == 0)
{
v___x_202_ = v_o_196_;
v_isShared_203_ = v_isSharedCheck_214_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_map_199_);
lean_dec(v_o_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_214_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_v_198_);
lean_inc(v_k_197_);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_197_, v___x_204_, v_map_199_);
if (v_hasTrace_200_ == 0)
{
lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_209_; 
v___x_206_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_207_ = l_Lean_Name_isPrefixOf(v___x_206_, v_k_197_);
lean_dec(v_k_197_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_209_ = v___x_202_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_205_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_207_);
return v___x_209_;
}
}
else
{
lean_object* v___x_212_; 
lean_dec(v_k_197_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_212_ = v___x_202_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_213_, sizeof(void*)*1, v_hasTrace_200_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption(lean_object* v_opts_222_, lean_object* v_decl_223_, lean_object* v_name_224_, lean_object* v_val_225_){
_start:
{
lean_object* v_defValue_227_; 
v_defValue_227_ = lean_ctor_get(v_decl_223_, 2);
lean_inc_ref(v_defValue_227_);
lean_dec_ref(v_decl_223_);
switch(lean_obj_tag(v_defValue_227_))
{
case 1:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
lean_dec_ref(v_defValue_227_);
v___x_228_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__0));
v___x_229_ = lean_string_dec_eq(v_val_225_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__1));
v___x_231_ = lean_string_dec_eq(v_val_225_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_name_224_);
lean_dec_ref(v_opts_222_);
v___x_232_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_233_ = lean_string_append(v___x_232_, v_val_225_);
lean_dec_ref(v_val_225_);
v___x_234_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__3));
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
v___x_236_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_val_225_);
v___x_238_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_222_, v_name_224_, v___x_229_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_val_225_);
v___x_240_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_222_, v_name_224_, v___x_229_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
case 3:
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_266_; 
v_isSharedCheck_266_ = !lean_is_exclusive(v_defValue_227_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v_defValue_227_, 0);
lean_dec(v_unused_267_);
v___x_243_ = v_defValue_227_;
v_isShared_244_ = v_isSharedCheck_266_;
goto v_resetjp_242_;
}
else
{
lean_dec(v_defValue_227_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_266_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_string_utf8_byte_size(v_val_225_);
lean_inc_ref(v_val_225_);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v_val_225_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
v___x_248_ = l_String_Slice_toNat_x3f(v___x_247_);
lean_dec_ref(v___x_247_);
if (lean_obj_tag(v___x_248_) == 1)
{
lean_object* v_val_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_257_; 
lean_del_object(v___x_243_);
lean_dec_ref(v_val_225_);
v_val_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_257_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_257_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_val_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_257_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(v_opts_222_, v_name_224_, v_val_249_);
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 0);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
lean_dec(v___x_248_);
lean_dec(v_name_224_);
lean_dec_ref(v_opts_222_);
v___x_258_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_259_ = lean_string_append(v___x_258_, v_val_225_);
lean_dec_ref(v_val_225_);
v___x_260_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__4));
v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 18);
lean_ctor_set(v___x_243_, 0, v___x_261_);
v___x_263_ = v___x_243_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
case 0:
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_275_; 
v_isSharedCheck_275_ = !lean_is_exclusive(v_defValue_227_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_defValue_227_, 0);
lean_dec(v_unused_276_);
v___x_269_ = v_defValue_227_;
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_defValue_227_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(v_opts_222_, v_name_224_, v_val_225_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
default: 
{
lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v_defValue_227_);
lean_dec_ref(v_val_225_);
lean_dec_ref(v_opts_222_);
v___x_277_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__5));
v___x_278_ = 1;
v___x_279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_224_, v___x_278_);
v___x_280_ = lean_string_append(v___x_277_, v___x_279_);
lean_dec_ref(v___x_279_);
v___x_281_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__6));
v___x_282_ = lean_string_append(v___x_280_, v___x_281_);
v___x_283_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption___boxed(lean_object* v_opts_285_, lean_object* v_decl_286_, lean_object* v_name_287_, lean_object* v_val_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Language_Lean_setOption(v_opts_285_, v_decl_286_, v_name_287_, v_val_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(lean_object* v_o_291_, lean_object* v_k_292_, lean_object* v_v_293_){
_start:
{
lean_object* v_map_294_; uint8_t v_hasTrace_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_308_; 
v_map_294_ = lean_ctor_get(v_o_291_, 0);
v_hasTrace_295_ = lean_ctor_get_uint8(v_o_291_, sizeof(void*)*1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_o_291_);
if (v_isSharedCheck_308_ == 0)
{
v___x_297_ = v_o_291_;
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_map_294_);
lean_dec(v_o_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; 
lean_inc(v_k_292_);
v___x_299_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_292_, v_v_293_, v_map_294_);
if (v_hasTrace_295_ == 0)
{
lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_301_ = l_Lean_Name_isPrefixOf(v___x_300_, v_k_292_);
lean_dec(v_k_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_303_ = v___x_297_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_299_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*1, v___x_301_);
return v___x_303_;
}
}
else
{
lean_object* v___x_306_; 
lean_dec(v_k_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*1, v_hasTrace_295_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object* v_a_315_, lean_object* v_init_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_d_320_; 
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; lean_object* v___x_327_; 
v_k_323_ = lean_ctor_get(v_x_317_, 1);
lean_inc(v_k_323_);
v_v_324_ = lean_ctor_get(v_x_317_, 2);
lean_inc(v_v_324_);
v_l_325_ = lean_ctor_get(v_x_317_, 3);
lean_inc(v_l_325_);
v_r_326_ = lean_ctor_get(v_x_317_, 4);
lean_inc(v_r_326_);
lean_dec_ref(v_x_317_);
v___x_327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_315_, v_init_316_, v_l_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v_a_329_; 
lean_dec_ref(v___x_327_);
lean_dec(v_r_326_);
lean_dec(v_v_324_);
lean_dec(v_k_323_);
v_a_329_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v_a_328_);
v_d_320_ = v_a_329_;
goto v___jp_319_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_381_; 
v_a_330_ = lean_ctor_get(v_a_328_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_381_ == 0)
{
v___x_332_ = v_a_328_;
v_isShared_333_ = v_isSharedCheck_381_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v_a_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_381_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_334_ = l_Lean_Name_getRoot(v_k_323_);
v___x_335_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1));
v___x_336_ = lean_box(0);
v___x_337_ = l_Lean_Name_replacePrefix(v_k_323_, v___x_335_, v___x_336_);
v___x_338_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_315_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_dec(v___x_334_);
lean_del_object(v___x_332_);
lean_dec_ref(v___x_327_);
if (lean_obj_tag(v_v_324_) == 0)
{
lean_object* v_val_339_; lean_object* v_v_340_; lean_object* v___x_341_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v___x_338_);
v_v_340_ = lean_ctor_get(v_v_324_, 0);
lean_inc_ref(v_v_340_);
lean_dec_ref(v_v_324_);
v___x_341_ = l_Lean_Language_Lean_setOption(v_a_330_, v_val_339_, v___x_337_, v_v_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
v_init_316_ = v_a_342_;
v_x_317_ = v_r_326_;
goto _start;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_r_326_);
v_a_344_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_341_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_338_);
v___x_352_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_a_330_, v___x_337_, v_v_324_);
v_init_316_ = v___x_352_;
v_x_317_ = v_r_326_;
goto _start;
}
}
else
{
uint8_t v___x_354_; 
lean_dec(v___x_338_);
lean_dec(v_a_330_);
lean_dec(v_v_324_);
v___x_354_ = lean_name_eq(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_354_ == 0)
{
lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_r_326_);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_327_, 0);
lean_dec(v_unused_376_);
v___x_356_ = v___x_327_;
v_isShared_357_ = v_isSharedCheck_375_;
goto v_resetjp_355_;
}
else
{
lean_dec(v___x_327_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_375_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_358_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2));
v___x_359_ = 1;
lean_inc(v___x_337_);
v___x_360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_337_, v___x_359_);
v___x_361_ = lean_string_append(v___x_358_, v___x_360_);
lean_dec_ref(v___x_360_);
v___x_362_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3));
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
v___x_364_ = l_Lean_Name_append(v___x_335_, v___x_337_);
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_364_, v___x_359_);
v___x_366_ = lean_string_append(v___x_363_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 18);
lean_ctor_set(v___x_332_, 0, v___x_368_);
v___x_370_ = v___x_332_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 1);
lean_ctor_set(v___x_356_, 0, v___x_370_);
v___x_372_ = v___x_356_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_dec(v___x_337_);
lean_del_object(v___x_332_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_377_; 
v_a_377_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_327_);
if (lean_obj_tag(v_a_377_) == 0)
{
lean_object* v_a_378_; 
lean_dec(v_r_326_);
v_a_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v_a_377_);
v_d_320_ = v_a_378_;
goto v___jp_319_;
}
else
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v_a_377_);
v_init_316_ = v_a_379_;
v_x_317_ = v_r_326_;
goto _start;
}
}
else
{
lean_dec(v_r_326_);
return v___x_327_;
}
}
}
}
}
}
else
{
lean_dec(v_r_326_);
lean_dec(v_v_324_);
lean_dec(v_k_323_);
return v___x_327_;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_init_316_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_d_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_a_384_, lean_object* v_init_385_, lean_object* v_x_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_384_, v_init_385_, v_x_386_);
lean_dec(v_a_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v_map_393_; lean_object* v_opts_x27_394_; lean_object* v___x_395_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref(v___x_391_);
v_map_393_ = lean_ctor_get(v_opts_389_, 0);
lean_inc(v_map_393_);
lean_dec_ref(v_opts_389_);
v_opts_x27_394_ = l_Lean_Options_empty;
v___x_395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_392_, v_opts_x27_394_, v_map_393_);
lean_dec(v_a_392_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_a_400_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_a_400_);
lean_dec(v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_a_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_395_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
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
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v_opts_389_);
v_a_413_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_391_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_391_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Language_Lean_reparseOptions(v_opts_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_432_){
_start:
{
lean_object* v_stx_434_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_437_);
v___x_439_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_440_ = l_Lean_Syntax_isOfKind(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
v_stx_434_ = v_stx_432_;
goto v___jp_433_;
}
else
{
lean_object* v___x_441_; lean_object* v_stx_442_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v_stx_442_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_441_);
lean_dec(v_stx_432_);
v_stx_434_ = v_stx_442_;
goto v___jp_433_;
}
v___jp_433_:
{
uint8_t v___x_435_; lean_object* v___x_436_; 
v___x_435_ = 0;
v___x_436_ = l_Lean_Syntax_getPos_x3f(v_stx_434_, v___x_435_);
lean_dec(v_stx_434_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_443_, lean_object* v_decl_444_, lean_object* v_ref_445_){
_start:
{
lean_object* v_defValue_447_; lean_object* v_descr_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_475_; 
v_defValue_447_ = lean_ctor_get(v_decl_444_, 0);
v_descr_448_ = lean_ctor_get(v_decl_444_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_decl_444_);
if (v_isSharedCheck_475_ == 0)
{
v___x_450_ = v_decl_444_;
v_isShared_451_ = v_isSharedCheck_475_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_descr_448_);
lean_inc(v_defValue_447_);
lean_dec(v_decl_444_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_475_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_alloc_ctor(1, 0, 1);
v___x_453_ = lean_unbox(v_defValue_447_);
lean_ctor_set_uint8(v___x_452_, 0, v___x_453_);
lean_inc_n(v_name_443_, 2);
v___x_454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_454_, 0, v_name_443_);
lean_ctor_set(v___x_454_, 1, v_ref_445_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
lean_ctor_set(v___x_454_, 3, v_descr_448_);
v___x_455_ = lean_register_option(v_name_443_, v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_465_; 
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_455_, 0);
lean_dec(v_unused_466_);
v___x_457_ = v___x_455_;
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_455_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v_defValue_447_);
lean_ctor_set(v___x_450_, 0, v_name_443_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_name_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_defValue_447_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_del_object(v___x_450_);
lean_dec(v_defValue_447_);
lean_dec(v_name_443_);
v_a_467_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_455_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_455_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_476_, lean_object* v_decl_477_, lean_object* v_ref_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_476_, v_decl_477_, v_ref_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_498_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_499_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_500_ = l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_497_, v___x_498_, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_502_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(32u);
v___x_504_ = lean_mk_empty_array_with_capacity(v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_506_ = ((size_t)5ULL);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_unsigned_to_nat(32u);
v___x_509_ = lean_mk_empty_array_with_capacity(v___x_508_);
v___x_510_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_511_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_509_);
lean_ctor_set(v___x_511_, 2, v___x_507_);
lean_ctor_set(v___x_511_, 3, v___x_507_);
lean_ctor_set_usize(v___x_511_, 4, v___x_506_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_infoState_515_; lean_object* v_trees_516_; lean_object* v___x_517_; lean_object* v_infoState_518_; lean_object* v_env_519_; lean_object* v_messages_520_; lean_object* v_scopes_521_; lean_object* v_usedQuotCtxts_522_; lean_object* v_nextMacroScope_523_; lean_object* v_maxRecDepth_524_; lean_object* v_ngen_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_snapshotTasks_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_549_; 
v___x_514_ = lean_st_ref_get(v___y_512_);
v_infoState_515_ = lean_ctor_get(v___x_514_, 8);
lean_inc_ref(v_infoState_515_);
lean_dec(v___x_514_);
v_trees_516_ = lean_ctor_get(v_infoState_515_, 2);
lean_inc_ref(v_trees_516_);
lean_dec_ref(v_infoState_515_);
v___x_517_ = lean_st_ref_take(v___y_512_);
v_infoState_518_ = lean_ctor_get(v___x_517_, 8);
v_env_519_ = lean_ctor_get(v___x_517_, 0);
v_messages_520_ = lean_ctor_get(v___x_517_, 1);
v_scopes_521_ = lean_ctor_get(v___x_517_, 2);
v_usedQuotCtxts_522_ = lean_ctor_get(v___x_517_, 3);
v_nextMacroScope_523_ = lean_ctor_get(v___x_517_, 4);
v_maxRecDepth_524_ = lean_ctor_get(v___x_517_, 5);
v_ngen_525_ = lean_ctor_get(v___x_517_, 6);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_517_, 7);
v_traceState_527_ = lean_ctor_get(v___x_517_, 9);
v_snapshotTasks_528_ = lean_ctor_get(v___x_517_, 10);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_549_ == 0)
{
v___x_530_ = v___x_517_;
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snapshotTasks_528_);
lean_inc(v_traceState_527_);
lean_inc(v_infoState_518_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_ngen_525_);
lean_inc(v_maxRecDepth_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_usedQuotCtxts_522_);
lean_inc(v_scopes_521_);
lean_inc(v_messages_520_);
lean_inc(v_env_519_);
lean_dec(v___x_517_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v_enabled_532_; lean_object* v_assignment_533_; lean_object* v_lazyAssignment_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_547_; 
v_enabled_532_ = lean_ctor_get_uint8(v_infoState_518_, sizeof(void*)*3);
v_assignment_533_ = lean_ctor_get(v_infoState_518_, 0);
v_lazyAssignment_534_ = lean_ctor_get(v_infoState_518_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_infoState_518_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_infoState_518_, 2);
lean_dec(v_unused_548_);
v___x_536_ = v_infoState_518_;
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_lazyAssignment_534_);
lean_inc(v_assignment_533_);
lean_dec(v_infoState_518_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 2, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_assignment_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_lazyAssignment_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v___x_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*3, v_enabled_532_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 8, v___x_540_);
v___x_542_ = v___x_530_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_519_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_messages_520_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_scopes_521_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_usedQuotCtxts_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_maxRecDepth_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_ngen_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 9, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 10, v_snapshotTasks_528_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_set(v___y_512_, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_trees_516_);
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_550_);
lean_dec(v___y_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_561_, lean_object* v_opt_562_){
_start:
{
lean_object* v_name_563_; lean_object* v_defValue_564_; lean_object* v_map_565_; lean_object* v___x_566_; 
v_name_563_ = lean_ctor_get(v_opt_562_, 0);
v_defValue_564_ = lean_ctor_get(v_opt_562_, 1);
v_map_565_ = lean_ctor_get(v_opts_561_, 0);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_565_, v_name_563_);
if (lean_obj_tag(v___x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = lean_unbox(v_defValue_564_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_568_);
lean_dec_ref(v___x_566_);
if (lean_obj_tag(v_val_568_) == 1)
{
uint8_t v_v_569_; 
v_v_569_ = lean_ctor_get_uint8(v_val_568_, 0);
lean_dec_ref(v_val_568_);
return v_v_569_;
}
else
{
uint8_t v___x_570_; 
lean_dec(v_val_568_);
v___x_570_ = lean_unbox(v_defValue_564_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_571_, lean_object* v_opt_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_571_, v_opt_572_);
lean_dec_ref(v_opt_572_);
lean_dec_ref(v_opts_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_val_577_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_581_, lean_object* v_val_582_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_inc_ref(v_val_582_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_583_, 0, v_val_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_inst_581_);
lean_ctor_set(v___x_584_, 1, v_val_582_);
v___x_585_ = lean_mk_thunk(v___f_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_589_);
lean_dec_ref(v___x_591_);
v___x_592_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_587_, v___y_588_, v___y_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_597_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_ctor_set(v___x_603_, 2, v___x_602_);
lean_ctor_set(v___x_603_, 3, v___x_601_);
lean_ctor_set(v___x_603_, 4, v___x_601_);
lean_ctor_set(v___x_603_, 5, v___x_601_);
lean_ctor_set(v___x_603_, 6, v___x_601_);
lean_ctor_set(v___x_603_, 7, v___x_601_);
lean_ctor_set(v___x_603_, 8, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(32u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_607_ = ((size_t)5ULL);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_unsigned_to_nat(32u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_612_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_608_);
lean_ctor_set(v___x_612_, 3, v___x_608_);
lean_ctor_set_usize(v___x_612_, 4, v___x_607_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_box(1);
v___x_614_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_env_621_; lean_object* v___x_622_; lean_object* v_scopes_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_opts_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_620_ = lean_st_ref_get(v___y_618_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_620_);
v___x_622_ = lean_st_ref_get(v___y_618_);
v_scopes_623_ = lean_ctor_get(v___x_622_, 2);
lean_inc(v_scopes_623_);
lean_dec(v___x_622_);
v___x_624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_625_ = l_List_head_x21___redArg(v___x_624_, v_scopes_623_);
lean_dec(v_scopes_623_);
v_opts_626_ = lean_ctor_get(v___x_625_, 1);
lean_inc_ref(v_opts_626_);
lean_dec(v___x_625_);
v___x_627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_629_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_629_, 0, v_env_621_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set(v___x_629_, 3, v_opts_626_);
v___x_630_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_msgData_617_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_632_, v___y_633_);
lean_dec(v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_636_, uint8_t v_suppressElabErrors_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 1)
{
lean_object* v_pre_639_; 
v_pre_639_ = lean_ctor_get(v_x_638_, 0);
if (lean_obj_tag(v_pre_639_) == 0)
{
lean_object* v_str_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_str_640_ = lean_ctor_get(v_x_638_, 1);
v___x_641_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_642_ = lean_string_dec_eq(v_str_640_, v___x_641_);
if (v___x_642_ == 0)
{
return v___y_636_;
}
else
{
return v_suppressElabErrors_637_;
}
}
else
{
return v___y_636_;
}
}
else
{
return v___y_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_643_, lean_object* v_suppressElabErrors_644_, lean_object* v_x_645_){
_start:
{
uint8_t v___y_9161__boxed_646_; uint8_t v_suppressElabErrors_boxed_647_; uint8_t v_res_648_; lean_object* v_r_649_; 
v___y_9161__boxed_646_ = lean_unbox(v___y_643_);
v_suppressElabErrors_boxed_647_ = lean_unbox(v_suppressElabErrors_644_);
v_res_648_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9161__boxed_646_, v_suppressElabErrors_boxed_647_, v_x_645_);
lean_dec(v_x_645_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_651_, lean_object* v_msgData_652_, uint8_t v_severity_653_, uint8_t v_isSilent_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_750_; lean_object* v___y_751_; uint8_t v___y_752_; uint8_t v___y_753_; lean_object* v___y_754_; uint8_t v___y_758_; uint8_t v___y_759_; uint8_t v___y_760_; uint8_t v___x_775_; uint8_t v___y_777_; uint8_t v___y_778_; uint8_t v___y_779_; uint8_t v___y_781_; uint8_t v___x_793_; 
v___x_775_ = 2;
v___x_793_ = l_Lean_instBEqMessageSeverity_beq(v_severity_653_, v___x_775_);
if (v___x_793_ == 0)
{
v___y_781_ = v___x_793_;
goto v___jp_780_;
}
else
{
uint8_t v___x_794_; 
lean_inc_ref(v_msgData_652_);
v___x_794_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_652_);
v___y_781_ = v___x_794_;
goto v___jp_780_;
}
v___jp_658_:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Elab_Command_getScope___redArg(v___y_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
v___x_669_ = l_Lean_Elab_Command_getScope___redArg(v___y_666_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_704_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_704_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_704_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_704_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v_currNamespace_675_; lean_object* v_openDecls_676_; lean_object* v_env_677_; lean_object* v_messages_678_; lean_object* v_scopes_679_; lean_object* v_usedQuotCtxts_680_; lean_object* v_nextMacroScope_681_; lean_object* v_maxRecDepth_682_; lean_object* v_ngen_683_; lean_object* v_auxDeclNGen_684_; lean_object* v_infoState_685_; lean_object* v_traceState_686_; lean_object* v_snapshotTasks_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_703_; 
v___x_674_ = lean_st_ref_take(v___y_666_);
v_currNamespace_675_ = lean_ctor_get(v_a_668_, 2);
lean_inc(v_currNamespace_675_);
lean_dec(v_a_668_);
v_openDecls_676_ = lean_ctor_get(v_a_670_, 3);
lean_inc(v_openDecls_676_);
lean_dec(v_a_670_);
v_env_677_ = lean_ctor_get(v___x_674_, 0);
v_messages_678_ = lean_ctor_get(v___x_674_, 1);
v_scopes_679_ = lean_ctor_get(v___x_674_, 2);
v_usedQuotCtxts_680_ = lean_ctor_get(v___x_674_, 3);
v_nextMacroScope_681_ = lean_ctor_get(v___x_674_, 4);
v_maxRecDepth_682_ = lean_ctor_get(v___x_674_, 5);
v_ngen_683_ = lean_ctor_get(v___x_674_, 6);
v_auxDeclNGen_684_ = lean_ctor_get(v___x_674_, 7);
v_infoState_685_ = lean_ctor_get(v___x_674_, 8);
v_traceState_686_ = lean_ctor_get(v___x_674_, 9);
v_snapshotTasks_687_ = lean_ctor_get(v___x_674_, 10);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_703_ == 0)
{
v___x_689_ = v___x_674_;
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snapshotTasks_687_);
lean_inc(v_traceState_686_);
lean_inc(v_infoState_685_);
lean_inc(v_auxDeclNGen_684_);
lean_inc(v_ngen_683_);
lean_inc(v_maxRecDepth_682_);
lean_inc(v_nextMacroScope_681_);
lean_inc(v_usedQuotCtxts_680_);
lean_inc(v_scopes_679_);
lean_inc(v_messages_678_);
lean_inc(v_env_677_);
lean_dec(v___x_674_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_currNamespace_675_);
lean_ctor_set(v___x_691_, 1, v_openDecls_676_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_661_);
lean_inc_ref(v___y_663_);
lean_inc_ref(v___y_662_);
v___x_693_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_693_, 0, v___y_662_);
lean_ctor_set(v___x_693_, 1, v___y_659_);
lean_ctor_set(v___x_693_, 2, v___y_664_);
lean_ctor_set(v___x_693_, 3, v___y_663_);
lean_ctor_set(v___x_693_, 4, v___x_692_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5, v___y_665_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5 + 1, v___y_660_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5 + 2, v_isSilent_654_);
v___x_694_ = l_Lean_MessageLog_add(v___x_693_, v_messages_678_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
v___x_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_env_677_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_scopes_679_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_usedQuotCtxts_680_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_nextMacroScope_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_maxRecDepth_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_ngen_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v_auxDeclNGen_684_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v_infoState_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 9, v_traceState_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 10, v_snapshotTasks_687_);
v___x_696_ = v_reuseFailAlloc_702_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_697_ = lean_st_ref_set(v___y_666_, v___x_696_);
v___x_698_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_698_);
v___x_700_ = v___x_672_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_a_668_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_659_);
v_a_705_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_669_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_669_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v___y_664_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_659_);
v_a_713_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_667_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_667_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
v___jp_721_:
{
lean_object* v_fileName_727_; lean_object* v_fileMap_728_; uint8_t v_suppressElabErrors_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_748_; 
v_fileName_727_ = lean_ctor_get(v___y_655_, 0);
v_fileMap_728_ = lean_ctor_get(v___y_655_, 1);
v_suppressElabErrors_729_ = lean_ctor_get_uint8(v___y_655_, sizeof(void*)*10);
v___x_730_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_652_);
v___x_731_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_730_, v___y_656_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_748_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_748_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_748_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc_ref_n(v_fileMap_728_, 2);
v___x_736_ = l_Lean_FileMap_toPosition(v_fileMap_728_, v___y_724_);
lean_dec(v___y_724_);
v___x_737_ = l_Lean_FileMap_toPosition(v_fileMap_728_, v___y_726_);
lean_dec(v___y_726_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_729_ == 0)
{
lean_del_object(v___x_734_);
v___y_659_ = v___x_736_;
v___y_660_ = v___y_723_;
v___y_661_ = v_a_732_;
v___y_662_ = v_fileName_727_;
v___y_663_ = v___x_739_;
v___y_664_ = v___x_738_;
v___y_665_ = v___y_725_;
v___y_666_ = v___y_656_;
goto v___jp_658_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___f_742_; uint8_t v___x_743_; 
v___x_740_ = lean_box(v___y_722_);
v___x_741_ = lean_box(v_suppressElabErrors_729_);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_742_, 0, v___x_740_);
lean_closure_set(v___f_742_, 1, v___x_741_);
lean_inc(v_a_732_);
v___x_743_ = l_Lean_MessageData_hasTag(v___f_742_, v_a_732_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v___x_736_);
lean_dec(v_a_732_);
v___x_744_ = lean_box(0);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_744_);
v___x_746_ = v___x_734_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_del_object(v___x_734_);
v___y_659_ = v___x_736_;
v___y_660_ = v___y_723_;
v___y_661_ = v_a_732_;
v___y_662_ = v_fileName_727_;
v___y_663_ = v___x_739_;
v___y_664_ = v___x_738_;
v___y_665_ = v___y_725_;
v___y_666_ = v___y_656_;
goto v___jp_658_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Syntax_getTailPos_x3f(v___y_751_, v___y_753_);
lean_dec(v___y_751_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_inc(v___y_754_);
v___y_722_ = v___y_750_;
v___y_723_ = v___y_752_;
v___y_724_ = v___y_754_;
v___y_725_ = v___y_753_;
v___y_726_ = v___y_754_;
goto v___jp_721_;
}
else
{
lean_object* v_val_756_; 
v_val_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_val_756_);
lean_dec_ref(v___x_755_);
v___y_722_ = v___y_750_;
v___y_723_ = v___y_752_;
v___y_724_ = v___y_754_;
v___y_725_ = v___y_753_;
v___y_726_ = v_val_756_;
goto v___jp_721_;
}
}
v___jp_757_:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Elab_Command_getRef___redArg(v___y_655_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v_ref_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v_ref_763_ = l_Lean_replaceRef(v_ref_651_, v_a_762_);
lean_dec(v_a_762_);
v___x_764_ = l_Lean_Syntax_getPos_x3f(v_ref_763_, v___y_759_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___y_750_ = v___y_758_;
v___y_751_ = v_ref_763_;
v___y_752_ = v___y_760_;
v___y_753_ = v___y_759_;
v___y_754_ = v___x_765_;
goto v___jp_749_;
}
else
{
lean_object* v_val_766_; 
v_val_766_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_766_);
lean_dec_ref(v___x_764_);
v___y_750_ = v___y_758_;
v___y_751_ = v_ref_763_;
v___y_752_ = v___y_760_;
v___y_753_ = v___y_759_;
v___y_754_ = v_val_766_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_msgData_652_);
v_a_767_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_761_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_761_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
v___jp_776_:
{
if (v___y_779_ == 0)
{
v___y_758_ = v___y_777_;
v___y_759_ = v___y_778_;
v___y_760_ = v_severity_653_;
goto v___jp_757_;
}
else
{
v___y_758_ = v___y_777_;
v___y_759_ = v___y_778_;
v___y_760_ = v___x_775_;
goto v___jp_757_;
}
}
v___jp_780_:
{
if (v___y_781_ == 0)
{
lean_object* v___x_782_; lean_object* v_scopes_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_opts_786_; uint8_t v___x_787_; uint8_t v___x_788_; 
v___x_782_ = lean_st_ref_get(v___y_656_);
v_scopes_783_ = lean_ctor_get(v___x_782_, 2);
lean_inc(v_scopes_783_);
lean_dec(v___x_782_);
v___x_784_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_785_ = l_List_head_x21___redArg(v___x_784_, v_scopes_783_);
lean_dec(v_scopes_783_);
v_opts_786_ = lean_ctor_get(v___x_785_, 1);
lean_inc_ref(v_opts_786_);
lean_dec(v___x_785_);
v___x_787_ = 1;
v___x_788_ = l_Lean_instBEqMessageSeverity_beq(v_severity_653_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec_ref(v_opts_786_);
v___y_777_ = v___y_781_;
v___y_778_ = v___y_781_;
v___y_779_ = v___x_788_;
goto v___jp_776_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = l_Lean_warningAsError;
v___x_790_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_786_, v___x_789_);
lean_dec_ref(v_opts_786_);
v___y_777_ = v___y_781_;
v___y_778_ = v___y_781_;
v___y_779_ = v___x_790_;
goto v___jp_776_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_msgData_652_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_795_, lean_object* v_msgData_796_, lean_object* v_severity_797_, lean_object* v_isSilent_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v_severity_boxed_802_; uint8_t v_isSilent_boxed_803_; lean_object* v_res_804_; 
v_severity_boxed_802_ = lean_unbox(v_severity_797_);
v_isSilent_boxed_803_ = lean_unbox(v_isSilent_798_);
v_res_804_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_795_, v_msgData_796_, v_severity_boxed_802_, v_isSilent_boxed_803_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v_ref_795_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_805_, uint8_t v_severity_806_, uint8_t v_isSilent_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Elab_Command_getRef___redArg(v___y_808_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_812_, v_msgData_805_, v_severity_806_, v_isSilent_807_, v___y_808_, v___y_809_);
lean_dec(v_a_812_);
return v___x_813_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_msgData_805_);
v_a_814_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_811_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_811_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_822_, lean_object* v_severity_823_, lean_object* v_isSilent_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v_severity_boxed_828_; uint8_t v_isSilent_boxed_829_; lean_object* v_res_830_; 
v_severity_boxed_828_ = lean_unbox(v_severity_823_);
v_isSilent_boxed_829_ = lean_unbox(v_isSilent_824_);
v_res_830_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_822_, v_severity_boxed_828_, v_isSilent_boxed_829_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; 
v___x_835_ = 2;
v___x_836_ = 0;
v___x_837_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_831_, v___x_835_, v___x_836_, v___y_832_, v___y_833_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_843_, lean_object* v_msgData_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = 2;
v___x_849_ = 0;
v___x_850_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_843_, v_msgData_844_, v___x_848_, v___x_849_, v___y_845_, v___y_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_851_, lean_object* v_msgData_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_851_, v_msgData_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v_ref_851_);
return v_res_856_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
if (lean_obj_tag(v_ex_860_) == 0)
{
lean_object* v_ref_864_; lean_object* v_msg_865_; lean_object* v___x_866_; 
v_ref_864_ = lean_ctor_get(v_ex_860_, 0);
lean_inc(v_ref_864_);
v_msg_865_ = lean_ctor_get(v_ex_860_, 1);
lean_inc_ref(v_msg_865_);
lean_dec_ref(v_ex_860_);
v___x_866_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_864_, v_msg_865_, v___y_861_, v___y_862_);
lean_dec(v_ref_864_);
return v___x_866_;
}
else
{
lean_object* v_id_867_; uint8_t v___y_869_; uint8_t v___x_891_; 
v_id_867_ = lean_ctor_get(v_ex_860_, 0);
lean_inc(v_id_867_);
v___x_891_ = l_Lean_Elab_isAbortExceptionId(v_id_867_);
if (v___x_891_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Exception_isInterrupt(v_ex_860_);
lean_dec_ref(v_ex_860_);
v___y_869_ = v___x_892_;
goto v___jp_868_;
}
else
{
lean_dec_ref(v_ex_860_);
v___y_869_ = v___x_891_;
goto v___jp_868_;
}
v___jp_868_:
{
if (v___y_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_InternalExceptionId_getName(v_id_867_);
lean_dec(v_id_867_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_873_ = l_Lean_MessageData_ofName(v_a_871_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_874_, v___y_861_, v___y_862_);
return v___x_875_;
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_888_; 
v_a_876_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_878_ = v___x_870_;
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_870_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_ref_880_ = lean_ctor_get(v___y_861_, 7);
v___x_881_ = lean_io_error_to_string(v_a_876_);
v___x_882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = l_Lean_MessageData_ofFormat(v___x_882_);
lean_inc(v_ref_880_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_ref_880_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_884_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
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
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_id_867_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
v___x_902_ = lean_apply_3(v_x_898_, v___y_899_, v___y_900_, lean_box(0));
if (lean_obj_tag(v___x_902_) == 0)
{
return v___x_902_;
}
else
{
lean_object* v_a_903_; uint8_t v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
v___x_904_ = l_Lean_Exception_isInterrupt(v_a_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec_ref(v___x_902_);
v___x_905_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_903_, v___y_899_, v___y_900_);
return v___x_905_;
}
else
{
lean_dec(v_a_903_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_911_, lean_object* v___x_912_, lean_object* v_val_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_a_917_; lean_object* v___x_919_; 
v___x_919_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_911_, v___x_912_, v_val_913_);
if (lean_obj_tag(v___x_919_) == 0)
{
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v_a_917_ = v_a_920_;
goto v___jp_916_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_919_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
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
else
{
lean_object* v___x_929_; 
lean_dec_ref(v___x_919_);
v___x_929_ = lean_box(0);
v_a_917_ = v___x_929_;
goto v___jp_916_;
}
v___jp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v_a_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_930_, lean_object* v___x_931_, lean_object* v_val_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_930_, v___x_931_, v_val_932_, v___y_933_);
lean_dec_ref(v___y_933_);
lean_dec(v_val_932_);
lean_dec_ref(v___x_931_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_936_, lean_object* v_x_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_get_set_stderr(v_h_936_);
lean_inc_ref(v___y_938_);
v___x_941_ = lean_apply_2(v_x_937_, v___y_938_, lean_box(0));
v___x_942_ = lean_get_set_stderr(v___x_940_);
lean_dec_ref(v___x_942_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_943_, v_x_944_, v___y_945_);
lean_dec_ref(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_948_, lean_object* v_h_949_, lean_object* v_x_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_949_, v_x_950_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_954_, lean_object* v_h_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_954_, v_h_955_, v_x_956_, v___y_957_);
lean_dec_ref(v___y_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_960_, lean_object* v_x_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_get_set_stdin(v_h_960_);
lean_inc_ref(v___y_962_);
v___x_965_ = lean_apply_2(v_x_961_, v___y_962_, lean_box(0));
v___x_966_ = lean_get_set_stdin(v___x_964_);
lean_dec_ref(v___x_966_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_967_, v_x_968_, v___y_969_);
lean_dec_ref(v___y_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_974_ = lean_panic_fn_borrowed(v___x_973_, v_msg_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_975_, lean_object* v_x_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_get_set_stdout(v_h_975_);
lean_inc_ref(v___y_977_);
v___x_980_ = lean_apply_2(v_x_976_, v___y_977_, lean_box(0));
v___x_981_ = lean_get_set_stdout(v___x_979_);
lean_dec_ref(v___x_981_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_982_, v_x_983_, v___y_984_);
lean_dec_ref(v___y_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_987_, lean_object* v_h_988_, lean_object* v_x_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_988_, v_x_989_, v___y_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_993_, lean_object* v_h_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_993_, v_h_994_, v_x_995_, v___y_996_);
lean_dec_ref(v___y_996_);
return v_res_998_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = l_ByteArray_empty;
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1005_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1006_ = lean_unsigned_to_nat(46u);
v___x_1007_ = lean_unsigned_to_nat(193u);
v___x_1008_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1009_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1010_ = l_mkPanicMessageWithDecl(v___x_1009_, v___x_1008_, v___x_1007_, v___x_1006_, v___x_1005_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1011_, uint8_t v_isolateStderr_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___y_1025_; 
v___x_1019_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1020_ = lean_st_mk_ref(v___x_1019_);
v___x_1021_ = lean_st_mk_ref(v___x_1019_);
v___x_1022_ = l_IO_FS_Stream_ofBuffer(v___x_1020_);
lean_inc(v___x_1021_);
v___x_1023_ = l_IO_FS_Stream_ofBuffer(v___x_1021_);
if (v_isolateStderr_1012_ == 0)
{
v___y_1025_ = v_x_1011_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1034_; 
lean_inc_ref(v___x_1023_);
v___x_1034_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1034_, 0, lean_box(0));
lean_closure_set(v___x_1034_, 1, v___x_1023_);
lean_closure_set(v___x_1034_, 2, v_x_1011_);
v___y_1025_ = v___x_1034_;
goto v___jp_1024_;
}
v___jp_1015_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___y_1017_);
lean_ctor_set(v___x_1018_, 1, v___y_1016_);
return v___x_1018_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_data_1029_; uint8_t v___x_1030_; 
v___x_1026_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1026_, 0, lean_box(0));
lean_closure_set(v___x_1026_, 1, v___x_1023_);
lean_closure_set(v___x_1026_, 2, v___y_1025_);
v___x_1027_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1022_, v___x_1026_, v___y_1013_);
v___x_1028_ = lean_st_ref_get(v___x_1021_);
lean_dec(v___x_1021_);
v_data_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_data_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_string_validate_utf8(v_data_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_data_1029_);
v___x_1031_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1032_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1031_);
v___y_1016_ = v___x_1027_;
v___y_1017_ = v___x_1032_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_string_from_utf8_unchecked(v_data_1029_);
v___y_1016_ = v___x_1027_;
v___y_1017_ = v___x_1033_;
goto v___jp_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1035_, lean_object* v_isolateStderr_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_isolateStderr_boxed_1039_; lean_object* v_res_1040_; 
v_isolateStderr_boxed_1039_ = lean_unbox(v_isolateStderr_1036_);
v_res_1040_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1035_, v_isolateStderr_boxed_1039_, v___y_1037_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = 1;
v___x_1050_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1051_ = l_Lean_Name_toString(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1052_, lean_object* v_cmdState_1053_, lean_object* v_beginPos_1054_, lean_object* v_snap_1055_, lean_object* v_cancelTk_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_env_1059_; lean_object* v_scopes_1060_; lean_object* v_usedQuotCtxts_1061_; lean_object* v_nextMacroScope_1062_; lean_object* v_maxRecDepth_1063_; lean_object* v_ngen_1064_; lean_object* v_auxDeclNGen_1065_; lean_object* v_infoState_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1142_; 
v_env_1059_ = lean_ctor_get(v_cmdState_1053_, 0);
v_scopes_1060_ = lean_ctor_get(v_cmdState_1053_, 2);
v_usedQuotCtxts_1061_ = lean_ctor_get(v_cmdState_1053_, 3);
v_nextMacroScope_1062_ = lean_ctor_get(v_cmdState_1053_, 4);
v_maxRecDepth_1063_ = lean_ctor_get(v_cmdState_1053_, 5);
v_ngen_1064_ = lean_ctor_get(v_cmdState_1053_, 6);
v_auxDeclNGen_1065_ = lean_ctor_get(v_cmdState_1053_, 7);
v_infoState_1066_ = lean_ctor_get(v_cmdState_1053_, 8);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_cmdState_1053_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1143_ = lean_ctor_get(v_cmdState_1053_, 10);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_cmdState_1053_, 9);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_cmdState_1053_, 1);
lean_dec(v_unused_1145_);
v___x_1068_ = v_cmdState_1053_;
v_isShared_1069_ = v_isSharedCheck_1142_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_infoState_1066_);
lean_inc(v_auxDeclNGen_1065_);
lean_inc(v_ngen_1064_);
lean_inc(v_maxRecDepth_1063_);
lean_inc(v_nextMacroScope_1062_);
lean_inc(v_usedQuotCtxts_1061_);
lean_inc(v_scopes_1060_);
lean_inc(v_env_1059_);
lean_dec(v_cmdState_1053_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1142_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1070_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1071_ = l_List_head_x21___redArg(v___x_1070_, v_scopes_1060_);
v___x_1072_ = l_Lean_MessageLog_empty;
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1075_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 10, v___x_1075_);
lean_ctor_set(v___x_1068_, 9, v___x_1074_);
lean_ctor_set(v___x_1068_, 1, v___x_1072_);
v___x_1077_ = v___x_1068_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_env_1059_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_scopes_1060_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_usedQuotCtxts_1061_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_nextMacroScope_1062_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_maxRecDepth_1063_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_ngen_1064_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_auxDeclNGen_1065_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_infoState_1066_);
lean_ctor_set(v_reuseFailAlloc_1141_, 9, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1141_, 10, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v_toProcessingContext_1079_; lean_object* v_fileName_1080_; lean_object* v_fileMap_1081_; lean_object* v_opts_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___y_1092_; uint8_t v___y_1093_; lean_object* v_messages_1094_; lean_object* v___y_1120_; 
v___x_1078_ = lean_st_mk_ref(v___x_1077_);
v_toProcessingContext_1079_ = lean_ctor_get(v_a_1057_, 0);
v_fileName_1080_ = lean_ctor_get(v_toProcessingContext_1079_, 1);
v_fileMap_1081_ = lean_ctor_get(v_toProcessingContext_1079_, 2);
v_opts_1082_ = lean_ctor_get(v___x_1071_, 1);
lean_inc_ref(v_opts_1082_);
lean_dec(v___x_1071_);
v___f_1083_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1083_, 0, v_stx_1052_);
v___x_1084_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_;
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Lean_firstFrontendMacroScope;
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Lean_internal_cmdlineSnapshots;
v___x_1090_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1082_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1140_; 
lean_inc_ref(v_snap_1055_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_snap_1055_);
v___y_1120_ = v___x_1140_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v___x_1086_;
goto v___jp_1119_;
}
v___jp_1091_:
{
lean_object* v_new_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_env_1101_; lean_object* v_scopes_1102_; lean_object* v_usedQuotCtxts_1103_; lean_object* v_nextMacroScope_1104_; lean_object* v_maxRecDepth_1105_; lean_object* v_ngen_1106_; lean_object* v_auxDeclNGen_1107_; lean_object* v_infoState_1108_; lean_object* v_traceState_1109_; lean_object* v_snapshotTasks_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_new_1095_ = lean_ctor_get(v_snap_1055_, 1);
lean_inc(v_new_1095_);
lean_dec_ref(v_snap_1055_);
v___x_1096_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1097_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1098_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
lean_ctor_set(v___x_1098_, 2, v___x_1086_);
lean_ctor_set(v___x_1098_, 3, v___x_1074_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*4, v___y_1093_);
v___x_1099_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1084_, v___x_1098_);
v___x_1100_ = lean_io_promise_resolve(v___x_1099_, v_new_1095_);
lean_dec(v_new_1095_);
v_env_1101_ = lean_ctor_get(v___y_1092_, 0);
v_scopes_1102_ = lean_ctor_get(v___y_1092_, 2);
v_usedQuotCtxts_1103_ = lean_ctor_get(v___y_1092_, 3);
v_nextMacroScope_1104_ = lean_ctor_get(v___y_1092_, 4);
v_maxRecDepth_1105_ = lean_ctor_get(v___y_1092_, 5);
v_ngen_1106_ = lean_ctor_get(v___y_1092_, 6);
v_auxDeclNGen_1107_ = lean_ctor_get(v___y_1092_, 7);
v_infoState_1108_ = lean_ctor_get(v___y_1092_, 8);
v_traceState_1109_ = lean_ctor_get(v___y_1092_, 9);
v_snapshotTasks_1110_ = lean_ctor_get(v___y_1092_, 10);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___y_1092_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___y_1092_, 1);
lean_dec(v_unused_1118_);
v___x_1112_ = v___y_1092_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_snapshotTasks_1110_);
lean_inc(v_traceState_1109_);
lean_inc(v_infoState_1108_);
lean_inc(v_auxDeclNGen_1107_);
lean_inc(v_ngen_1106_);
lean_inc(v_maxRecDepth_1105_);
lean_inc(v_nextMacroScope_1104_);
lean_inc(v_usedQuotCtxts_1103_);
lean_inc(v_scopes_1102_);
lean_inc(v_env_1101_);
lean_dec(v___y_1092_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_messages_1094_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_env_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_messages_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_scopes_1102_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_usedQuotCtxts_1103_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_nextMacroScope_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_maxRecDepth_1105_);
lean_ctor_set(v_reuseFailAlloc_1116_, 6, v_ngen_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 7, v_auxDeclNGen_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 8, v_infoState_1108_);
lean_ctor_set(v_reuseFailAlloc_1116_, 9, v_traceState_1109_);
lean_ctor_set(v_reuseFailAlloc_1116_, 10, v_snapshotTasks_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
v___jp_1119_:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v_fst_1128_; lean_object* v___x_1129_; lean_object* v_messages_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_cancelTk_1056_);
v___x_1122_ = 0;
lean_inc(v_beginPos_1054_);
lean_inc_ref(v_fileMap_1081_);
lean_inc_ref(v_fileName_1080_);
v___x_1123_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1123_, 0, v_fileName_1080_);
lean_ctor_set(v___x_1123_, 1, v_fileMap_1081_);
lean_ctor_set(v___x_1123_, 2, v___x_1073_);
lean_ctor_set(v___x_1123_, 3, v_beginPos_1054_);
lean_ctor_set(v___x_1123_, 4, v___x_1085_);
lean_ctor_set(v___x_1123_, 5, v___x_1086_);
lean_ctor_set(v___x_1123_, 6, v___x_1087_);
lean_ctor_set(v___x_1123_, 7, v___x_1088_);
lean_ctor_set(v___x_1123_, 8, v___y_1120_);
lean_ctor_set(v___x_1123_, 9, v___x_1121_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*10, v___x_1122_);
lean_inc(v___x_1078_);
v___f_1124_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1124_, 0, v___f_1083_);
lean_closure_set(v___f_1124_, 1, v___x_1123_);
lean_closure_set(v___f_1124_, 2, v___x_1078_);
v___x_1125_ = l_Lean_Core_stderrAsMessages;
v___x_1126_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1082_, v___x_1125_);
lean_dec_ref(v_opts_1082_);
v___x_1127_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1124_, v___x_1126_, v_a_1057_);
v_fst_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_fst_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = lean_st_ref_get(v___x_1078_);
lean_dec(v___x_1078_);
v_messages_1130_ = lean_ctor_get(v___x_1129_, 1);
lean_inc_ref(v_messages_1130_);
v___x_1131_ = lean_string_utf8_byte_size(v_fst_1128_);
v___x_1132_ = lean_nat_dec_eq(v___x_1131_, v___x_1073_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc_ref(v_fileMap_1081_);
v___x_1133_ = l_Lean_FileMap_toPosition(v_fileMap_1081_, v_beginPos_1054_);
lean_dec(v_beginPos_1054_);
v___x_1134_ = 0;
v___x_1135_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_fst_1128_);
v___x_1137_ = l_Lean_MessageData_ofFormat(v___x_1136_);
lean_inc_ref(v_fileName_1080_);
v___x_1138_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1138_, 0, v_fileName_1080_);
lean_ctor_set(v___x_1138_, 1, v___x_1133_);
lean_ctor_set(v___x_1138_, 2, v___x_1086_);
lean_ctor_set(v___x_1138_, 3, v___x_1135_);
lean_ctor_set(v___x_1138_, 4, v___x_1137_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*5, v___x_1122_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*5 + 1, v___x_1134_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*5 + 2, v___x_1122_);
v___x_1139_ = l_Lean_MessageLog_add(v___x_1138_, v_messages_1130_);
v___y_1092_ = v___x_1129_;
v___y_1093_ = v___x_1122_;
v_messages_1094_ = v___x_1139_;
goto v___jp_1091_;
}
else
{
lean_dec(v_fst_1128_);
lean_dec(v_beginPos_1054_);
v___y_1092_ = v___x_1129_;
v___y_1093_ = v___x_1122_;
v_messages_1094_ = v_messages_1130_;
goto v___jp_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1146_, lean_object* v_cmdState_1147_, lean_object* v_beginPos_1148_, lean_object* v_snap_1149_, lean_object* v_cancelTk_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1146_, v_cmdState_1147_, v_beginPos_1148_, v_snap_1149_, v_cancelTk_1150_, v_a_1151_);
lean_dec_ref(v_a_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1154_, lean_object* v_h_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1155_, v_x_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_h_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1160_, v_h_1161_, v_x_1162_, v___y_1163_);
lean_dec_ref(v___y_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1166_, lean_object* v_x_1167_, uint8_t v_isolateStderr_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1167_, v_isolateStderr_1168_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_x_1173_, lean_object* v_isolateStderr_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_isolateStderr_boxed_1177_; lean_object* v_res_1178_; 
v_isolateStderr_boxed_1177_ = lean_unbox(v_isolateStderr_1174_);
v_res_1178_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1172_, v_x_1173_, v_isolateStderr_boxed_1177_, v___y_1175_);
lean_dec_ref(v___y_1175_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1179_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_opts_1189_, lean_object* v_opt_1190_){
_start:
{
lean_object* v_name_1191_; lean_object* v_defValue_1192_; lean_object* v_map_1193_; lean_object* v___x_1194_; 
v_name_1191_ = lean_ctor_get(v_opt_1190_, 0);
v_defValue_1192_ = lean_ctor_get(v_opt_1190_, 1);
v_map_1193_ = lean_ctor_get(v_opts_1189_, 0);
v___x_1194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1193_, v_name_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_inc(v_defValue_1192_);
return v_defValue_1192_;
}
else
{
lean_object* v_val_1195_; 
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref(v___x_1194_);
if (lean_obj_tag(v_val_1195_) == 3)
{
lean_object* v_v_1196_; 
v_v_1196_ = lean_ctor_get(v_val_1195_, 0);
lean_inc(v_v_1196_);
lean_dec_ref(v_val_1195_);
return v_v_1196_;
}
else
{
lean_dec(v_val_1195_);
lean_inc(v_defValue_1192_);
return v_defValue_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0___boxed(lean_object* v_opts_1197_, lean_object* v_opt_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1197_, v_opt_1198_);
lean_dec_ref(v_opt_1198_);
lean_dec_ref(v_opts_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_s_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_s_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_s_1203_){
_start:
{
lean_object* v_toSnapshot_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_toSnapshot_1204_ = lean_ctor_get(v_s_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_s_1203_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_s_1203_, 1);
lean_dec(v_unused_1213_);
v___x_1206_ = v_s_1203_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_toSnapshot_1204_);
lean_dec(v_s_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_toSnapshot_1204_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_s_1214_){
_start:
{
lean_object* v_tree_1215_; lean_object* v___x_1216_; 
v_tree_1215_ = lean_ctor_get(v_s_1214_, 1);
v___x_1216_ = lean_thunk_get_own(v_tree_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_s_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_s_1217_);
lean_dec_ref(v_s_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v_a_1219_, lean_object* v___x_1220_, lean_object* v_parserState_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_toProcessingContext_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_toProcessingContext_1223_ = lean_ctor_get(v_a_1219_, 0);
v___x_1224_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1223_);
v___x_1225_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1223_, v___x_1220_, v_parserState_1221_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v_a_1226_, lean_object* v___x_1227_, lean_object* v_parserState_1228_, lean_object* v_x_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v_a_1226_, v___x_1227_, v_parserState_1228_, v_x_1229_);
lean_dec_ref(v_a_1226_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v___x_1233_, uint8_t v_val_1234_, lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1231_);
return v_b_1238_;
}
else
{
lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1259_; 
v_snd_1241_ = lean_ctor_get(v_b_1238_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_b_1238_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_b_1238_, 0);
lean_dec(v_unused_1260_);
v___x_1243_ = v_b_1238_;
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_dec(v_b_1238_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_a_1245_; lean_object* v_msg_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v_a_1245_ = lean_array_uget_borrowed(v_as_1235_, v_i_1237_);
v_msg_1246_ = lean_ctor_get(v_a_1245_, 1);
v___x_1247_ = lean_box(0);
lean_inc_ref(v___x_1231_);
v___x_1248_ = l_Lean_FileMap_toPosition(v___x_1231_, v___x_1232_);
v___x_1249_ = 0;
v___x_1250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1246_);
lean_inc_ref(v___x_1233_);
v___x_1251_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1251_, 0, v___x_1233_);
lean_ctor_set(v___x_1251_, 1, v___x_1248_);
lean_ctor_set(v___x_1251_, 2, v___x_1247_);
lean_ctor_set(v___x_1251_, 3, v___x_1250_);
lean_ctor_set(v___x_1251_, 4, v_msg_1246_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*5, v_val_1234_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*5 + 1, v___x_1249_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*5 + 2, v_val_1234_);
v___x_1252_ = l_Lean_MessageLog_add(v___x_1251_, v_snd_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1252_);
lean_ctor_set(v___x_1243_, 0, v___x_1247_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
size_t v___x_1255_; size_t v___x_1256_; 
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1237_, v___x_1255_);
v_i_1237_ = v___x_1256_;
v_b_1238_ = v___x_1254_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v___x_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v_val_1264_, lean_object* v_as_1265_, lean_object* v_sz_1266_, lean_object* v_i_1267_, lean_object* v_b_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v_val_44557__boxed_1270_; size_t v_sz_boxed_1271_; size_t v_i_boxed_1272_; lean_object* v_res_1273_; 
v_val_44557__boxed_1270_ = lean_unbox(v_val_1264_);
v_sz_boxed_1271_ = lean_unbox_usize(v_sz_1266_);
lean_dec(v_sz_1266_);
v_i_boxed_1272_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1261_, v___x_1262_, v___x_1263_, v_val_44557__boxed_1270_, v_as_1265_, v_sz_boxed_1271_, v_i_boxed_1272_, v_b_1268_);
lean_dec_ref(v_as_1265_);
lean_dec(v___x_1262_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, uint8_t v_val_1277_, lean_object* v_as_1278_, size_t v_sz_1279_, size_t v_i_1280_, lean_object* v_b_1281_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_lt(v_i_1280_, v_sz_1279_);
if (v___x_1283_ == 0)
{
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1274_);
return v_b_1281_;
}
else
{
lean_object* v_snd_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1302_; 
v_snd_1284_ = lean_ctor_get(v_b_1281_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_b_1281_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_b_1281_, 0);
lean_dec(v_unused_1303_);
v___x_1286_ = v_b_1281_;
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_snd_1284_);
lean_dec(v_b_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_a_1288_; lean_object* v_msg_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v_a_1288_ = lean_array_uget_borrowed(v_as_1278_, v_i_1280_);
v_msg_1289_ = lean_ctor_get(v_a_1288_, 1);
v___x_1290_ = lean_box(0);
lean_inc_ref(v___x_1274_);
v___x_1291_ = l_Lean_FileMap_toPosition(v___x_1274_, v___x_1275_);
v___x_1292_ = 0;
v___x_1293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1289_);
lean_inc_ref(v___x_1276_);
v___x_1294_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1294_, 0, v___x_1276_);
lean_ctor_set(v___x_1294_, 1, v___x_1291_);
lean_ctor_set(v___x_1294_, 2, v___x_1290_);
lean_ctor_set(v___x_1294_, 3, v___x_1293_);
lean_ctor_set(v___x_1294_, 4, v_msg_1289_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*5, v_val_1277_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*5 + 1, v___x_1292_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*5 + 2, v_val_1277_);
v___x_1295_ = l_Lean_MessageLog_add(v___x_1294_, v_snd_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1295_);
lean_ctor_set(v___x_1286_, 0, v___x_1290_);
v___x_1297_ = v___x_1286_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1280_, v___x_1298_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1274_, v___x_1275_, v___x_1276_, v_val_1277_, v_as_1278_, v_sz_1279_, v___x_1299_, v___x_1297_);
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v_val_1307_, lean_object* v_as_1308_, lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_val_44609__boxed_1313_; size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_val_44609__boxed_1313_ = lean_unbox(v_val_1307_);
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1304_, v___x_1305_, v___x_1306_, v_val_44609__boxed_1313_, v_as_1308_, v_sz_boxed_1314_, v_i_boxed_1315_, v_b_1311_);
lean_dec_ref(v_as_1308_);
lean_dec(v___x_1305_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object* v_init_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v___x_1320_, uint8_t v_val_1321_, lean_object* v_n_1322_, lean_object* v_b_1323_){
_start:
{
if (lean_obj_tag(v_n_1322_) == 0)
{
lean_object* v_cs_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1340_; 
v_cs_1325_ = lean_ctor_get(v_n_1322_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_n_1322_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1327_ = v_n_1322_;
v_isShared_1328_ = v_isSharedCheck_1340_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_cs_1325_);
lean_dec(v_n_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1340_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v_fst_1334_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v_b_1323_);
v_sz_1331_ = lean_array_size(v_cs_1325_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1317_, v___x_1318_, v___x_1319_, v___x_1320_, v_val_1321_, v_cs_1325_, v_sz_1331_, v___x_1332_, v___x_1330_);
lean_dec_ref(v_cs_1325_);
v_fst_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_fst_1334_);
if (lean_obj_tag(v_fst_1334_) == 0)
{
lean_object* v_snd_1335_; lean_object* v___x_1337_; 
v_snd_1335_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1333_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 0, v_snd_1335_);
v___x_1337_ = v___x_1327_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_snd_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v_val_1339_; 
lean_dec_ref(v___x_1333_);
lean_del_object(v___x_1327_);
v_val_1339_ = lean_ctor_get(v_fst_1334_, 0);
lean_inc(v_val_1339_);
lean_dec_ref(v_fst_1334_);
return v_val_1339_;
}
}
}
else
{
lean_object* v_vs_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_vs_1341_ = lean_ctor_get(v_n_1322_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_n_1322_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1343_ = v_n_1322_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_vs_1341_);
lean_dec(v_n_1322_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; lean_object* v_fst_1350_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_b_1323_);
v_sz_1347_ = lean_array_size(v_vs_1341_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1318_, v___x_1319_, v___x_1320_, v_val_1321_, v_vs_1341_, v_sz_1347_, v___x_1348_, v___x_1346_);
lean_dec_ref(v_vs_1341_);
v_fst_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_fst_1350_);
if (lean_obj_tag(v_fst_1350_) == 0)
{
lean_object* v_snd_1351_; lean_object* v___x_1353_; 
v_snd_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1349_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_snd_1351_);
v___x_1353_ = v___x_1343_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_snd_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_val_1355_; 
lean_dec_ref(v___x_1349_);
lean_del_object(v___x_1343_);
v_val_1355_ = lean_ctor_get(v_fst_1350_, 0);
lean_inc(v_val_1355_);
lean_dec_ref(v_fst_1350_);
return v_val_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v_init_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, uint8_t v_val_1361_, lean_object* v_as_1362_, size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_b_1365_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1367_ == 0)
{
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1358_);
return v_b_1365_;
}
else
{
lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1386_; 
v_snd_1368_ = lean_ctor_get(v_b_1365_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_b_1365_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_b_1365_, 0);
lean_dec(v_unused_1387_);
v___x_1370_ = v_b_1365_;
v_isShared_1371_ = v_isSharedCheck_1386_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_dec(v_b_1365_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1386_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1372_ = lean_array_uget_borrowed(v_as_1362_, v_i_1364_);
lean_inc(v_snd_1368_);
lean_inc(v_a_1372_);
lean_inc_ref(v___x_1360_);
lean_inc_ref(v___x_1358_);
v___x_1373_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1357_, v___x_1358_, v___x_1359_, v___x_1360_, v_val_1361_, v_a_1372_, v_snd_1368_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1358_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1374_);
v___x_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_snd_1368_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec(v_snd_1368_);
v_a_1378_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1373_);
v___x_1379_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_a_1378_);
lean_ctor_set(v___x_1370_, 0, v___x_1379_);
v___x_1381_ = v___x_1370_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_a_1378_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
size_t v___x_1382_; size_t v___x_1383_; 
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1364_, v___x_1382_);
v_i_1364_ = v___x_1383_;
v_b_1365_ = v___x_1381_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v_val_1392_, lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_val_44660__boxed_1398_; size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_val_44660__boxed_1398_ = lean_unbox(v_val_1392_);
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1388_, v___x_1389_, v___x_1390_, v___x_1391_, v_val_44660__boxed_1398_, v_as_1393_, v_sz_boxed_1399_, v_i_boxed_1400_, v_b_1396_);
lean_dec_ref(v_as_1393_);
lean_dec(v___x_1390_);
lean_dec_ref(v_init_1388_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v_init_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_val_1406_, lean_object* v_n_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_val_44676__boxed_1410_; lean_object* v_res_1411_; 
v_val_44676__boxed_1410_ = lean_unbox(v_val_1406_);
v_res_1411_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1402_, v___x_1403_, v___x_1404_, v___x_1405_, v_val_44676__boxed_1410_, v_n_1407_, v_b_1408_);
lean_dec(v___x_1404_);
lean_dec_ref(v_init_1402_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, uint8_t v_val_1415_, lean_object* v_as_1416_, size_t v_sz_1417_, size_t v_i_1418_, lean_object* v_b_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1418_, v_sz_1417_);
if (v___x_1421_ == 0)
{
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1412_);
return v_b_1419_;
}
else
{
lean_object* v_snd_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1440_; 
v_snd_1422_ = lean_ctor_get(v_b_1419_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_b_1419_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_b_1419_, 0);
lean_dec(v_unused_1441_);
v___x_1424_ = v_b_1419_;
v_isShared_1425_ = v_isSharedCheck_1440_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_snd_1422_);
lean_dec(v_b_1419_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1440_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_a_1426_; lean_object* v_msg_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_a_1426_ = lean_array_uget_borrowed(v_as_1416_, v_i_1418_);
v_msg_1427_ = lean_ctor_get(v_a_1426_, 1);
v___x_1428_ = lean_box(0);
lean_inc_ref(v___x_1412_);
v___x_1429_ = l_Lean_FileMap_toPosition(v___x_1412_, v___x_1413_);
v___x_1430_ = 0;
v___x_1431_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1427_);
lean_inc_ref(v___x_1414_);
v___x_1432_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1432_, 0, v___x_1414_);
lean_ctor_set(v___x_1432_, 1, v___x_1429_);
lean_ctor_set(v___x_1432_, 2, v___x_1428_);
lean_ctor_set(v___x_1432_, 3, v___x_1431_);
lean_ctor_set(v___x_1432_, 4, v_msg_1427_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*5, v_val_1415_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*5 + 1, v___x_1430_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*5 + 2, v_val_1415_);
v___x_1433_ = l_Lean_MessageLog_add(v___x_1432_, v_snd_1422_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v___x_1433_);
lean_ctor_set(v___x_1424_, 0, v___x_1428_);
v___x_1435_ = v___x_1424_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
size_t v___x_1436_; size_t v___x_1437_; 
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1418_, v___x_1436_);
v_i_1418_ = v___x_1437_;
v_b_1419_ = v___x_1435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v_val_1445_, lean_object* v_as_1446_, lean_object* v_sz_1447_, lean_object* v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_val_44782__boxed_1451_; size_t v_sz_boxed_1452_; size_t v_i_boxed_1453_; lean_object* v_res_1454_; 
v_val_44782__boxed_1451_ = lean_unbox(v_val_1445_);
v_sz_boxed_1452_ = lean_unbox_usize(v_sz_1447_);
lean_dec(v_sz_1447_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1442_, v___x_1443_, v___x_1444_, v_val_44782__boxed_1451_, v_as_1446_, v_sz_boxed_1452_, v_i_boxed_1453_, v_b_1449_);
lean_dec_ref(v_as_1446_);
lean_dec(v___x_1443_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, uint8_t v_val_1458_, lean_object* v_as_1459_, size_t v_sz_1460_, size_t v_i_1461_, lean_object* v_b_1462_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_usize_dec_lt(v_i_1461_, v_sz_1460_);
if (v___x_1464_ == 0)
{
lean_dec_ref(v___x_1457_);
lean_dec_ref(v___x_1455_);
return v_b_1462_;
}
else
{
lean_object* v_snd_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1483_; 
v_snd_1465_ = lean_ctor_get(v_b_1462_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_b_1462_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_b_1462_, 0);
lean_dec(v_unused_1484_);
v___x_1467_ = v_b_1462_;
v_isShared_1468_ = v_isSharedCheck_1483_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snd_1465_);
lean_dec(v_b_1462_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1483_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_a_1469_; lean_object* v_msg_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v_a_1469_ = lean_array_uget_borrowed(v_as_1459_, v_i_1461_);
v_msg_1470_ = lean_ctor_get(v_a_1469_, 1);
v___x_1471_ = lean_box(0);
lean_inc_ref(v___x_1455_);
v___x_1472_ = l_Lean_FileMap_toPosition(v___x_1455_, v___x_1456_);
v___x_1473_ = 0;
v___x_1474_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1470_);
lean_inc_ref(v___x_1457_);
v___x_1475_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1475_, 0, v___x_1457_);
lean_ctor_set(v___x_1475_, 1, v___x_1472_);
lean_ctor_set(v___x_1475_, 2, v___x_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1474_);
lean_ctor_set(v___x_1475_, 4, v_msg_1470_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*5, v_val_1458_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*5 + 1, v___x_1473_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*5 + 2, v_val_1458_);
v___x_1476_ = l_Lean_MessageLog_add(v___x_1475_, v_snd_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___x_1476_);
lean_ctor_set(v___x_1467_, 0, v___x_1471_);
v___x_1478_ = v___x_1467_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
size_t v___x_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1461_, v___x_1479_);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1455_, v___x_1456_, v___x_1457_, v_val_1458_, v_as_1459_, v_sz_1460_, v___x_1480_, v___x_1478_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v___x_1487_, lean_object* v_val_1488_, lean_object* v_as_1489_, lean_object* v_sz_1490_, lean_object* v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v_val_44834__boxed_1494_; size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_val_44834__boxed_1494_ = lean_unbox(v_val_1488_);
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1490_);
lean_dec(v_sz_1490_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1485_, v___x_1486_, v___x_1487_, v_val_44834__boxed_1494_, v_as_1489_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1492_);
lean_dec_ref(v_as_1489_);
lean_dec(v___x_1486_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, uint8_t v_val_1501_, lean_object* v_t_1502_, lean_object* v_init_1503_){
_start:
{
lean_object* v_root_1505_; lean_object* v_tail_1506_; lean_object* v___x_1507_; 
v_root_1505_ = lean_ctor_get(v_t_1502_, 0);
lean_inc_ref(v_root_1505_);
v_tail_1506_ = lean_ctor_get(v_t_1502_, 1);
lean_inc_ref(v_tail_1506_);
lean_dec_ref(v_t_1502_);
lean_inc_ref(v___x_1500_);
lean_inc_ref(v___x_1498_);
lean_inc_ref(v_init_1503_);
v___x_1507_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1503_, v___x_1498_, v___x_1499_, v___x_1500_, v_val_1501_, v_root_1505_, v_init_1503_);
lean_dec_ref(v_init_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
lean_dec_ref(v_tail_1506_);
lean_dec_ref(v___x_1500_);
lean_dec_ref(v___x_1498_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
return v_a_1508_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; size_t v_sz_1512_; size_t v___x_1513_; lean_object* v___x_1514_; lean_object* v_fst_1515_; 
v_a_1509_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1507_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v_a_1509_);
v_sz_1512_ = lean_array_size(v_tail_1506_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1498_, v___x_1499_, v___x_1500_, v_val_1501_, v_tail_1506_, v_sz_1512_, v___x_1513_, v___x_1511_);
lean_dec_ref(v_tail_1506_);
v_fst_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_fst_1515_);
if (lean_obj_tag(v_fst_1515_) == 0)
{
lean_object* v_snd_1516_; 
v_snd_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_snd_1516_);
lean_dec_ref(v___x_1514_);
return v_snd_1516_;
}
else
{
lean_object* v_val_1517_; 
lean_dec_ref(v___x_1514_);
v_val_1517_ = lean_ctor_get(v_fst_1515_, 0);
lean_inc(v_val_1517_);
lean_dec_ref(v_fst_1515_);
return v_val_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_val_1521_, lean_object* v_t_1522_, lean_object* v_init_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v_val_44885__boxed_1525_; lean_object* v_res_1526_; 
v_val_44885__boxed_1525_ = lean_unbox(v_val_1521_);
v_res_1526_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1518_, v___x_1519_, v___x_1520_, v_val_44885__boxed_1525_, v_t_1522_, v_init_1523_);
lean_dec(v___x_1519_);
return v_res_1526_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = l_Lean_firstFrontendMacroScope;
v___x_1529_ = lean_nat_add(v___x_1528_, v___x_1527_);
return v___x_1529_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, size_t v___x_1544_, uint8_t v___x_1545_, lean_object* v_env_1546_, lean_object* v___x_1547_, lean_object* v___x_1548_, lean_object* v_a_1549_, lean_object* v_opts_1550_, lean_object* v___x_1551_, lean_object* v_pos_1552_, uint8_t v_val_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v___x_1556_, lean_object* v___x_1557_, uint8_t v___x_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_toProcessingContext_1580_; lean_object* v_fileName_1581_; lean_object* v_fileMap_1582_; lean_object* v_env_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v_fileName_1589_; lean_object* v_fileMap_1590_; lean_object* v_currRecDepth_1591_; lean_object* v_ref_1592_; lean_object* v_currNamespace_1593_; lean_object* v_openDecls_1594_; lean_object* v_initHeartbeats_1595_; lean_object* v_maxHeartbeats_1596_; lean_object* v_quotContext_1597_; lean_object* v_currMacroScope_1598_; lean_object* v_cancelTk_x3f_1599_; uint8_t v_suppressElabErrors_1600_; lean_object* v_inheritedTraceOptions_1601_; lean_object* v___y_1602_; uint8_t v___y_1619_; uint8_t v___x_1639_; 
v___x_1561_ = l_Lean_firstFrontendMacroScope;
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1564_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1565_ = lean_box(0);
lean_inc(v___x_1541_);
v___x_1566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1541_);
lean_ctor_set(v___x_1566_, 1, v___x_1562_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
v___x_1567_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1568_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1542_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_inc_n(v___x_1543_, 2);
v___x_1571_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1543_);
lean_ctor_set(v___x_1571_, 3, v___x_1543_);
lean_ctor_set_usize(v___x_1571_, 4, v___x_1544_);
v___x_1572_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1571_, 2);
v___x_1573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
lean_ctor_set(v___x_1573_, 2, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1567_);
lean_ctor_set(v___x_1574_, 1, v___x_1567_);
lean_ctor_set(v___x_1574_, 2, v___x_1571_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*3, v___x_1545_);
v___x_1575_ = lean_mk_empty_array_with_capacity(v___x_1543_);
lean_inc_ref(v___x_1575_);
lean_inc_ref(v___x_1547_);
v___x_1576_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1576_, 0, v_env_1546_);
lean_ctor_set(v___x_1576_, 1, v___x_1563_);
lean_ctor_set(v___x_1576_, 2, v___x_1564_);
lean_ctor_set(v___x_1576_, 3, v___x_1566_);
lean_ctor_set(v___x_1576_, 4, v___x_1547_);
lean_ctor_set(v___x_1576_, 5, v___x_1568_);
lean_ctor_set(v___x_1576_, 6, v___x_1573_);
lean_ctor_set(v___x_1576_, 7, v___x_1574_);
lean_ctor_set(v___x_1576_, 8, v___x_1575_);
v___x_1577_ = lean_st_mk_ref(v___x_1576_);
v___x_1578_ = lean_st_ref_get(v___x_1548_);
v___x_1579_ = lean_st_ref_get(v___x_1577_);
v_toProcessingContext_1580_ = lean_ctor_get(v_a_1549_, 0);
v_fileName_1581_ = lean_ctor_get(v_toProcessingContext_1580_, 1);
v_fileMap_1582_ = lean_ctor_get(v_toProcessingContext_1580_, 2);
v_env_1583_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_ref(v_env_1583_);
lean_dec(v___x_1579_);
v___x_1584_ = lean_box(0);
v___x_1585_ = l_Lean_Core_getMaxHeartbeats(v_opts_1550_);
v___x_1586_ = l_Lean_diagnostics;
v___x_1587_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1550_, v___x_1586_);
v___x_1639_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1583_);
lean_dec_ref(v_env_1583_);
if (v___x_1639_ == 0)
{
if (v___x_1587_ == 0)
{
v___y_1619_ = v___x_1558_;
goto v___jp_1618_;
}
else
{
v___y_1619_ = v___x_1639_;
goto v___jp_1618_;
}
}
else
{
v___y_1619_ = v___x_1587_;
goto v___jp_1618_;
}
v___jp_1588_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = l_Lean_maxRecDepth;
v___x_1604_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1550_, v___x_1603_);
lean_inc(v_currMacroScope_1598_);
lean_inc(v_openDecls_1594_);
lean_inc(v_ref_1592_);
v___x_1605_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1605_, 0, v_fileName_1589_);
lean_ctor_set(v___x_1605_, 1, v_fileMap_1590_);
lean_ctor_set(v___x_1605_, 2, v_opts_1550_);
lean_ctor_set(v___x_1605_, 3, v_currRecDepth_1591_);
lean_ctor_set(v___x_1605_, 4, v___x_1604_);
lean_ctor_set(v___x_1605_, 5, v_ref_1592_);
lean_ctor_set(v___x_1605_, 6, v_currNamespace_1593_);
lean_ctor_set(v___x_1605_, 7, v_openDecls_1594_);
lean_ctor_set(v___x_1605_, 8, v_initHeartbeats_1595_);
lean_ctor_set(v___x_1605_, 9, v_maxHeartbeats_1596_);
lean_ctor_set(v___x_1605_, 10, v_quotContext_1597_);
lean_ctor_set(v___x_1605_, 11, v_currMacroScope_1598_);
lean_ctor_set(v___x_1605_, 12, v_cancelTk_x3f_1599_);
lean_ctor_set(v___x_1605_, 13, v_inheritedTraceOptions_1601_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*14, v___x_1587_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*14 + 1, v_suppressElabErrors_1600_);
v___x_1606_ = l_Lean_Language_SnapshotTree_trace(v___x_1551_, v___x_1605_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; lean_object* v_traceState_1608_; lean_object* v_traces_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v___x_1556_);
v___x_1607_ = lean_st_ref_get(v___x_1577_);
lean_dec(v___x_1577_);
v_traceState_1608_ = lean_ctor_get(v___x_1607_, 4);
lean_inc_ref(v_traceState_1608_);
lean_dec(v___x_1607_);
v_traces_1609_ = lean_ctor_get(v_traceState_1608_, 0);
lean_inc_ref(v_traces_1609_);
lean_dec_ref(v_traceState_1608_);
v___x_1610_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1581_);
lean_inc_ref(v_fileMap_1582_);
v___x_1611_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1582_, v_pos_1552_, v_fileName_1581_, v_val_1553_, v_traces_1609_, v___x_1610_);
v___x_1612_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1613_, 0, v___x_1554_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
lean_ctor_set(v___x_1613_, 2, v___x_1555_);
lean_ctor_set(v___x_1613_, 3, v___x_1547_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*4, v_val_1553_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1575_);
v___x_1615_ = lean_task_pure(v___x_1614_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___x_1606_);
lean_dec(v___x_1577_);
lean_dec(v___x_1555_);
lean_dec_ref(v___x_1554_);
lean_dec_ref(v___x_1547_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1556_);
lean_ctor_set(v___x_1616_, 1, v___x_1575_);
v___x_1617_ = lean_task_pure(v___x_1616_);
return v___x_1617_;
}
}
v___jp_1618_:
{
if (v___y_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v_env_1621_; lean_object* v_nextMacroScope_1622_; lean_object* v_ngen_1623_; lean_object* v_auxDeclNGen_1624_; lean_object* v_traceState_1625_; lean_object* v_messages_1626_; lean_object* v_infoState_1627_; lean_object* v_snapshotTasks_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v___x_1620_ = lean_st_ref_take(v___x_1577_);
v_env_1621_ = lean_ctor_get(v___x_1620_, 0);
v_nextMacroScope_1622_ = lean_ctor_get(v___x_1620_, 1);
v_ngen_1623_ = lean_ctor_get(v___x_1620_, 2);
v_auxDeclNGen_1624_ = lean_ctor_get(v___x_1620_, 3);
v_traceState_1625_ = lean_ctor_get(v___x_1620_, 4);
v_messages_1626_ = lean_ctor_get(v___x_1620_, 6);
v_infoState_1627_ = lean_ctor_get(v___x_1620_, 7);
v_snapshotTasks_1628_ = lean_ctor_get(v___x_1620_, 8);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v___x_1620_, 5);
lean_dec(v_unused_1638_);
v___x_1630_ = v___x_1620_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snapshotTasks_1628_);
lean_inc(v_infoState_1627_);
lean_inc(v_messages_1626_);
lean_inc(v_traceState_1625_);
lean_inc(v_auxDeclNGen_1624_);
lean_inc(v_ngen_1623_);
lean_inc(v_nextMacroScope_1622_);
lean_inc(v_env_1621_);
lean_dec(v___x_1620_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lean_Kernel_enableDiag(v_env_1621_, v___x_1587_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 5, v___x_1568_);
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_nextMacroScope_1622_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_ngen_1623_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_auxDeclNGen_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_traceState_1625_);
lean_ctor_set(v_reuseFailAlloc_1636_, 5, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1636_, 6, v_messages_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 7, v_infoState_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 8, v_snapshotTasks_1628_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_st_ref_set(v___x_1577_, v___x_1634_);
lean_inc(v___x_1577_);
lean_inc(v___x_1541_);
lean_inc(v___x_1543_);
lean_inc_ref(v_fileMap_1582_);
lean_inc_ref(v_fileName_1581_);
v_fileName_1589_ = v_fileName_1581_;
v_fileMap_1590_ = v_fileMap_1582_;
v_currRecDepth_1591_ = v___x_1543_;
v_ref_1592_ = v___x_1584_;
v_currNamespace_1593_ = v___x_1541_;
v_openDecls_1594_ = v___x_1565_;
v_initHeartbeats_1595_ = v___x_1543_;
v_maxHeartbeats_1596_ = v___x_1585_;
v_quotContext_1597_ = v___x_1541_;
v_currMacroScope_1598_ = v___x_1561_;
v_cancelTk_x3f_1599_ = v___x_1557_;
v_suppressElabErrors_1600_ = v_val_1553_;
v_inheritedTraceOptions_1601_ = v___x_1578_;
v___y_1602_ = v___x_1577_;
goto v___jp_1588_;
}
}
}
else
{
lean_inc(v___x_1577_);
lean_inc(v___x_1541_);
lean_inc(v___x_1543_);
lean_inc_ref(v_fileMap_1582_);
lean_inc_ref(v_fileName_1581_);
v_fileName_1589_ = v_fileName_1581_;
v_fileMap_1590_ = v_fileMap_1582_;
v_currRecDepth_1591_ = v___x_1543_;
v_ref_1592_ = v___x_1584_;
v_currNamespace_1593_ = v___x_1541_;
v_openDecls_1594_ = v___x_1565_;
v_initHeartbeats_1595_ = v___x_1543_;
v_maxHeartbeats_1596_ = v___x_1585_;
v_quotContext_1597_ = v___x_1541_;
v_currMacroScope_1598_ = v___x_1561_;
v_cancelTk_x3f_1599_ = v___x_1557_;
v_suppressElabErrors_1600_ = v_val_1553_;
v_inheritedTraceOptions_1601_ = v___x_1578_;
v___y_1602_ = v___x_1577_;
goto v___jp_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1640_ = _args[0];
lean_object* v___x_1641_ = _args[1];
lean_object* v___x_1642_ = _args[2];
lean_object* v___x_1643_ = _args[3];
lean_object* v___x_1644_ = _args[4];
lean_object* v_env_1645_ = _args[5];
lean_object* v___x_1646_ = _args[6];
lean_object* v___x_1647_ = _args[7];
lean_object* v_a_1648_ = _args[8];
lean_object* v_opts_1649_ = _args[9];
lean_object* v___x_1650_ = _args[10];
lean_object* v_pos_1651_ = _args[11];
lean_object* v_val_1652_ = _args[12];
lean_object* v___x_1653_ = _args[13];
lean_object* v___x_1654_ = _args[14];
lean_object* v___x_1655_ = _args[15];
lean_object* v___x_1656_ = _args[16];
lean_object* v___x_1657_ = _args[17];
lean_object* v_x_1658_ = _args[18];
lean_object* v___y_1659_ = _args[19];
_start:
{
size_t v___x_44946__boxed_1660_; uint8_t v___x_44947__boxed_1661_; uint8_t v_val_44951__boxed_1662_; uint8_t v___x_44956__boxed_1663_; lean_object* v_res_1664_; 
v___x_44946__boxed_1660_ = lean_unbox_usize(v___x_1643_);
lean_dec(v___x_1643_);
v___x_44947__boxed_1661_ = lean_unbox(v___x_1644_);
v_val_44951__boxed_1662_ = lean_unbox(v_val_1652_);
v___x_44956__boxed_1663_ = lean_unbox(v___x_1657_);
v_res_1664_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1640_, v___x_1641_, v___x_1642_, v___x_44946__boxed_1660_, v___x_44947__boxed_1661_, v_env_1645_, v___x_1646_, v___x_1647_, v_a_1648_, v_opts_1649_, v___x_1650_, v_pos_1651_, v_val_44951__boxed_1662_, v___x_1653_, v___x_1654_, v___x_1655_, v___x_1656_, v___x_44956__boxed_1663_, v_x_1658_);
lean_dec(v_pos_1651_);
lean_dec_ref(v_a_1648_);
lean_dec(v___x_1647_);
lean_dec(v___x_1641_);
return v_res_1664_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1671_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1672_ = l_Lean_Name_append(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1673_, lean_object* v___x_1674_, uint8_t v_val_1675_, lean_object* v_val_1676_, lean_object* v_val_1677_, lean_object* v___x_1678_, lean_object* v___x_1679_, uint8_t v___x_1680_, lean_object* v_a_1681_, lean_object* v_pos_1682_, lean_object* v_infoSt_1683_){
_start:
{
lean_object* v___y_1686_; lean_object* v_msgLog_1687_; lean_object* v___y_1693_; lean_object* v_trees_1725_; lean_object* v_size_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_trees_1725_ = lean_ctor_get(v_infoSt_1683_, 2);
v_size_1726_ = lean_ctor_get(v_trees_1725_, 2);
v___x_1727_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1728_ = lean_nat_dec_lt(v___x_1679_, v_size_1726_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
v___x_1729_ = l_outOfBounds___redArg(v___x_1727_);
v___y_1693_ = v___x_1729_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1727_, v_trees_1725_, v___x_1679_);
v___y_1693_ = v___x_1730_;
goto v___jp_1692_;
}
v___jp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1687_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___y_1686_);
v___x_1690_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1673_);
lean_ctor_set(v___x_1690_, 1, v___x_1688_);
lean_ctor_set(v___x_1690_, 2, v___x_1689_);
lean_ctor_set(v___x_1690_, 3, v___x_1674_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*4, v_val_1675_);
v___x_1691_ = lean_io_promise_resolve(v___x_1690_, v_val_1676_);
return v___x_1691_;
}
v___jp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_scopes_1696_; lean_object* v___x_1697_; lean_object* v_opts_1698_; uint8_t v_hasTrace_1699_; lean_object* v___x_1700_; 
v___x_1694_ = l_Lean_inheritedTraceOptions;
v___x_1695_ = lean_st_ref_get(v___x_1694_);
v_scopes_1696_ = lean_ctor_get(v_val_1677_, 2);
v___x_1697_ = l_List_head_x21___redArg(v___x_1678_, v_scopes_1696_);
v_opts_1698_ = lean_ctor_get(v___x_1697_, 1);
lean_inc_ref(v_opts_1698_);
lean_dec(v___x_1697_);
v_hasTrace_1699_ = lean_ctor_get_uint8(v_opts_1698_, sizeof(void*)*1);
v___x_1700_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1699_ == 0)
{
lean_dec_ref(v_opts_1698_);
lean_dec(v___x_1695_);
lean_dec(v___x_1679_);
v___y_1686_ = v___y_1693_;
v_msgLog_1687_ = v___x_1700_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1701_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1702_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1703_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1695_, v_opts_1698_, v___x_1703_);
lean_dec_ref(v_opts_1698_);
lean_dec(v___x_1695_);
if (v___x_1704_ == 0)
{
lean_dec(v___x_1679_);
v___y_1686_ = v___y_1693_;
v_msgLog_1687_ = v___x_1700_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_box(0);
lean_inc_ref(v___y_1693_);
v___x_1706_ = l_Lean_Elab_InfoTree_format(v___y_1693_, v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; double v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_toProcessingContext_1711_; lean_object* v_fileName_1712_; lean_object* v_fileMap_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = lean_float_of_nat(v___x_1679_);
v___x_1709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1710_, 0, v___x_1701_);
lean_ctor_set(v___x_1710_, 1, v___x_1705_);
lean_ctor_set(v___x_1710_, 2, v___x_1709_);
lean_ctor_set_float(v___x_1710_, sizeof(void*)*3, v___x_1708_);
lean_ctor_set_float(v___x_1710_, sizeof(void*)*3 + 8, v___x_1708_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*3 + 16, v___x_1680_);
v_toProcessingContext_1711_ = lean_ctor_get(v_a_1681_, 0);
v_fileName_1712_ = lean_ctor_get(v_toProcessingContext_1711_, 1);
v_fileMap_1713_ = lean_ctor_get(v_toProcessingContext_1711_, 2);
v___x_1714_ = l_Lean_MessageData_nil;
v___x_1715_ = l_Lean_MessageData_ofFormat(v_a_1707_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_mk_empty_array_with_capacity(v___x_1716_);
v___x_1718_ = lean_array_push(v___x_1717_, v___x_1715_);
v___x_1719_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1710_);
lean_ctor_set(v___x_1719_, 1, v___x_1714_);
lean_ctor_set(v___x_1719_, 2, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1702_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_inc_ref(v_fileMap_1713_);
v___x_1721_ = l_Lean_FileMap_toPosition(v_fileMap_1713_, v_pos_1682_);
v___x_1722_ = 0;
lean_inc_ref(v_fileName_1712_);
v___x_1723_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1723_, 0, v_fileName_1712_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
lean_ctor_set(v___x_1723_, 2, v___x_1705_);
lean_ctor_set(v___x_1723_, 3, v___x_1709_);
lean_ctor_set(v___x_1723_, 4, v___x_1720_);
lean_ctor_set_uint8(v___x_1723_, sizeof(void*)*5, v_val_1675_);
lean_ctor_set_uint8(v___x_1723_, sizeof(void*)*5 + 1, v___x_1722_);
lean_ctor_set_uint8(v___x_1723_, sizeof(void*)*5 + 2, v_val_1675_);
v___x_1724_ = l_Lean_MessageLog_add(v___x_1723_, v___x_1700_);
v___y_1686_ = v___y_1693_;
v_msgLog_1687_ = v___x_1724_;
goto v___jp_1685_;
}
else
{
lean_dec_ref(v___x_1706_);
lean_dec(v___x_1679_);
v___y_1686_ = v___y_1693_;
v_msgLog_1687_ = v___x_1700_;
goto v___jp_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1731_, lean_object* v___x_1732_, lean_object* v_val_1733_, lean_object* v_val_1734_, lean_object* v_val_1735_, lean_object* v___x_1736_, lean_object* v___x_1737_, lean_object* v___x_1738_, lean_object* v_a_1739_, lean_object* v_pos_1740_, lean_object* v_infoSt_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v_val_45133__boxed_1743_; uint8_t v___x_45138__boxed_1744_; lean_object* v_res_1745_; 
v_val_45133__boxed_1743_ = lean_unbox(v_val_1733_);
v___x_45138__boxed_1744_ = lean_unbox(v___x_1738_);
v_res_1745_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1731_, v___x_1732_, v_val_45133__boxed_1743_, v_val_1734_, v_val_1735_, v___x_1736_, v___x_1737_, v___x_45138__boxed_1744_, v_a_1739_, v_pos_1740_, v_infoSt_1741_);
lean_dec_ref(v_infoSt_1741_);
lean_dec(v_pos_1740_);
lean_dec_ref(v_a_1739_);
lean_dec_ref(v___x_1736_);
lean_dec_ref(v_val_1735_);
lean_dec(v_val_1734_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1747_, size_t v_i_1748_, size_t v_stop_1749_, lean_object* v_b_1750_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_eq(v_i_1748_, v_stop_1749_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; 
v___x_1753_ = lean_array_uget_borrowed(v_as_1747_, v_i_1748_);
v___f_1754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1753_);
v___x_1755_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1754_, v___x_1753_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1748_, v___x_1756_);
v_i_1748_ = v___x_1757_;
v_b_1750_ = v___x_1755_;
goto _start;
}
else
{
return v_b_1750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1759_, lean_object* v_i_1760_, lean_object* v_stop_1761_, lean_object* v_b_1762_, lean_object* v___y_1763_){
_start:
{
size_t v_i_boxed_1764_; size_t v_stop_boxed_1765_; lean_object* v_res_1766_; 
v_i_boxed_1764_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_stop_boxed_1765_ = lean_unbox_usize(v_stop_1761_);
lean_dec(v_stop_1761_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1759_, v_i_boxed_1764_, v_stop_boxed_1765_, v_b_1762_);
lean_dec_ref(v_as_1759_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1767_, lean_object* v_newParserState_1768_, lean_object* v_val_1769_, lean_object* v_sync_1770_, lean_object* v_val_1771_, lean_object* v_a_1772_, lean_object* v_oldNext_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v_sync_boxed_1775_; lean_object* v_res_1776_; 
v_sync_boxed_1775_ = lean_unbox(v_sync_1770_);
v_res_1776_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1767_, v_newParserState_1768_, v_val_1769_, v_sync_boxed_1775_, v_val_1771_, v_a_1772_, v_oldNext_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1777_, lean_object* v_newParserState_1778_, lean_object* v_val_1779_, uint8_t v_sync_1780_, lean_object* v_val_1781_, lean_object* v_a_1782_, lean_object* v_oldResult_1783_){
_start:
{
lean_object* v_task_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
v_task_1785_ = lean_ctor_get(v_val_1777_, 3);
lean_inc_ref(v_task_1785_);
lean_dec_ref(v_val_1777_);
v___x_1786_ = lean_box(v_sync_1780_);
lean_inc_ref(v_a_1782_);
v___f_1787_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1787_, 0, v_oldResult_1783_);
lean_closure_set(v___f_1787_, 1, v_newParserState_1778_);
lean_closure_set(v___f_1787_, 2, v_val_1779_);
lean_closure_set(v___f_1787_, 3, v___x_1786_);
lean_closure_set(v___f_1787_, 4, v_val_1781_);
lean_closure_set(v___f_1787_, 5, v_a_1782_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = 1;
v___x_1790_ = l_BaseIO_chainTask___redArg(v_task_1785_, v___f_1787_, v___x_1788_, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1791_, lean_object* v_newParserState_1792_, lean_object* v_val_1793_, lean_object* v_sync_1794_, lean_object* v_val_1795_, lean_object* v_a_1796_, lean_object* v_oldResult_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v_sync_boxed_1799_; lean_object* v_res_1800_; 
v_sync_boxed_1799_ = lean_unbox(v_sync_1794_);
v_res_1800_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1791_, v_newParserState_1792_, v_val_1793_, v_sync_boxed_1799_, v_val_1795_, v_a_1796_, v_oldResult_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1800_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1803_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1802_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1805_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1814_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1815_ = l_Lean_Name_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1819_, lean_object* v_val_1820_, lean_object* v_fst_1821_, uint8_t v_val_1822_, lean_object* v_a_1823_, lean_object* v_snd_1824_, lean_object* v___x_1825_, uint8_t v___x_1826_, lean_object* v_fst_1827_, lean_object* v_val_1828_, lean_object* v_val_1829_, lean_object* v_val_1830_, lean_object* v_snd_1831_, lean_object* v_prom_1832_, lean_object* v___x_1833_, lean_object* v___f_1834_, lean_object* v___f_1835_, lean_object* v___f_1836_, lean_object* v_pos_1837_, lean_object* v_fst_1838_, lean_object* v_cmdState_1839_, lean_object* v_opts_1840_, lean_object* v___x_1841_, lean_object* v_old_x3f_1842_, lean_object* v_parseCancelTk_1843_, lean_object* v_next_x3f_1844_){
_start:
{
lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v_snapshotTasks_1852_; lean_object* v_traceTask_1853_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; size_t v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v_env_1889_; lean_object* v_messages_1890_; lean_object* v_scopes_1891_; lean_object* v_infoState_1892_; lean_object* v_traceState_1893_; lean_object* v_snapshotTasks_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v_reportedCmdState_1902_; size_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v_reportedCmdState_1959_; size_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; size_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2022_; 
if (lean_obj_tag(v_next_x3f_1844_) == 0)
{
lean_object* v___x_2075_; 
lean_dec(v_parseCancelTk_1843_);
v___x_2075_ = lean_box(0);
v___y_2022_ = v___x_2075_;
goto v___jp_2021_;
}
else
{
lean_object* v_toProcessingContext_2076_; lean_object* v_val_2077_; lean_object* v_pos_2078_; lean_object* v_endPos_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_toProcessingContext_2076_ = lean_ctor_get(v_a_1823_, 0);
v_val_2077_ = lean_ctor_get(v_next_x3f_1844_, 0);
v_pos_2078_ = lean_ctor_get(v_fst_1821_, 0);
v_endPos_2079_ = lean_ctor_get(v_toProcessingContext_2076_, 3);
v___x_2080_ = lean_box(0);
lean_inc(v_endPos_2079_);
lean_inc(v_pos_2078_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_pos_2078_);
lean_ctor_set(v___x_2081_, 1, v_endPos_2079_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_parseCancelTk_1843_);
v___x_2084_ = l_IO_Promise_result_x21___redArg(v_val_2077_);
v___x_2085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2080_);
lean_ctor_set(v___x_2085_, 1, v___x_2082_);
lean_ctor_set(v___x_2085_, 2, v___x_2083_);
lean_ctor_set(v___x_2085_, 3, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___y_2022_ = v___x_2086_;
goto v___jp_2021_;
}
v___jp_1846_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1854_, 0, v___y_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1819_);
lean_ctor_set(v___x_1854_, 2, v___y_1847_);
lean_ctor_set(v___x_1854_, 3, v_traceTask_1853_);
v___x_1855_ = lean_array_push(v_snapshotTasks_1852_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___y_1848_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_io_promise_resolve(v___x_1856_, v_val_1820_);
if (lean_obj_tag(v_next_x3f_1844_) == 1)
{
lean_object* v_val_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_val_1858_ = lean_ctor_get(v_next_x3f_1844_, 0);
lean_inc(v_val_1858_);
lean_dec_ref(v_next_x3f_1844_);
v___x_1859_ = lean_box(0);
v___x_1860_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1859_, v_fst_1821_, v___y_1851_, v_val_1858_, v_val_1822_, v___y_1849_, v_a_1823_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1849_);
lean_dec(v_next_x3f_1844_);
lean_dec_ref(v_fst_1821_);
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
}
v___jp_1862_:
{
lean_object* v_snapshotTasks_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_snapshotTasks_1869_ = lean_ctor_get(v___y_1868_, 10);
lean_inc_ref(v_snapshotTasks_1869_);
v___x_1870_ = lean_mk_empty_array_with_capacity(v___y_1865_);
lean_dec(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___y_1864_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_task_pure(v___x_1871_);
v___y_1847_ = v___y_1863_;
v___y_1848_ = v___y_1864_;
v___y_1849_ = v___y_1867_;
v___y_1850_ = v___y_1866_;
v___y_1851_ = v___y_1868_;
v_snapshotTasks_1852_ = v_snapshotTasks_1869_;
v_traceTask_1853_ = v___x_1872_;
goto v___jp_1846_;
}
v___jp_1873_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_opts_1912_; uint8_t v_hasTrace_1913_; 
v___x_1903_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1890_);
v___x_1904_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1904_, 0, v___y_1885_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
lean_ctor_set(v___x_1904_, 2, v___y_1895_);
lean_ctor_set(v___x_1904_, 3, v_traceState_1893_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*4, v_val_1822_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v_reportedCmdState_1902_);
v___x_1906_ = lean_io_promise_resolve(v___x_1905_, v_val_1829_);
v___x_1907_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1892_);
lean_inc(v___y_1900_);
v___x_1908_ = l_BaseIO_chainTask___redArg(v___x_1907_, v___y_1899_, v___y_1900_, v___x_1826_);
v___x_1909_ = l_Lean_inheritedTraceOptions;
v___x_1910_ = lean_st_ref_get(v___x_1909_);
v___x_1911_ = l_List_head_x21___redArg(v___x_1833_, v_scopes_1891_);
lean_dec(v_scopes_1891_);
lean_dec_ref(v___x_1833_);
v_opts_1912_ = lean_ctor_get(v___x_1911_, 1);
lean_inc_ref(v_opts_1912_);
lean_dec(v___x_1911_);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_opts_1912_, sizeof(void*)*1);
if (v_hasTrace_1913_ == 0)
{
lean_dec_ref(v_opts_1912_);
lean_dec(v___x_1910_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_snapshotTasks_1894_);
lean_dec_ref(v_env_1889_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v_pos_1837_);
lean_dec_ref(v___f_1836_);
lean_dec_ref(v___f_1835_);
lean_dec_ref(v___f_1834_);
lean_dec(v___x_1825_);
v___y_1863_ = v___y_1897_;
v___y_1864_ = v___y_1901_;
v___y_1865_ = v___y_1900_;
v___y_1866_ = v___y_1886_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___y_1888_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1910_, v_opts_1912_, v___x_1914_);
lean_dec(v___x_1910_);
if (v___x_1915_ == 0)
{
lean_dec_ref(v_opts_1912_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_snapshotTasks_1894_);
lean_dec_ref(v_env_1889_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v_pos_1837_);
lean_dec_ref(v___f_1836_);
lean_dec_ref(v___f_1835_);
lean_dec_ref(v___f_1834_);
lean_dec(v___x_1825_);
v___y_1863_ = v___y_1897_;
v___y_1864_ = v___y_1901_;
v___y_1865_ = v___y_1900_;
v___y_1866_ = v___y_1886_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___y_1888_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
lean_inc_n(v___y_1900_, 3);
v___x_1916_ = lean_task_map(v___f_1834_, v___y_1896_, v___y_1900_, v___x_1826_);
lean_inc_n(v___y_1897_, 3);
lean_inc_n(v___y_1898_, 2);
lean_inc_n(v___y_1884_, 2);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v___y_1884_);
lean_ctor_set(v___x_1917_, 1, v___y_1898_);
lean_ctor_set(v___x_1917_, 2, v___y_1897_);
lean_ctor_set(v___x_1917_, 3, v___x_1916_);
v___x_1918_ = lean_task_map(v___f_1835_, v___y_1883_, v___y_1900_, v___x_1826_);
v___x_1919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1919_, 0, v___y_1884_);
lean_ctor_set(v___x_1919_, 1, v___y_1898_);
lean_ctor_set(v___x_1919_, 2, v___y_1897_);
lean_ctor_set(v___x_1919_, 3, v___x_1918_);
v___x_1920_ = lean_task_map(v___f_1836_, v___y_1882_, v___y_1900_, v___x_1826_);
v___x_1921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1921_, 0, v___y_1884_);
lean_ctor_set(v___x_1921_, 1, v___y_1898_);
lean_ctor_set(v___x_1921_, 2, v___y_1897_);
lean_ctor_set(v___x_1921_, 3, v___x_1920_);
v___x_1922_ = lean_unsigned_to_nat(3u);
v___x_1923_ = lean_mk_empty_array_with_capacity(v___x_1922_);
v___x_1924_ = lean_array_push(v___x_1923_, v___x_1917_);
v___x_1925_ = lean_array_push(v___x_1924_, v___x_1919_);
v___x_1926_ = lean_array_push(v___x_1925_, v___x_1921_);
v___x_1927_ = l_Array_append___redArg(v___x_1926_, v_snapshotTasks_1894_);
lean_inc_ref(v___y_1901_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1901_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
lean_inc_ref(v___x_1928_);
v___x_1929_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1928_);
v___x_1930_ = lean_box_usize(v___y_1874_);
v___x_1931_ = lean_box(v___x_1826_);
v___x_1932_ = lean_box(v_val_1822_);
v___x_1933_ = lean_box(v___x_1915_);
lean_inc_ref(v_a_1823_);
lean_inc_ref(v___y_1881_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_1934_, 0, v___x_1825_);
lean_closure_set(v___f_1934_, 1, v___y_1879_);
lean_closure_set(v___f_1934_, 2, v___y_1878_);
lean_closure_set(v___f_1934_, 3, v___x_1930_);
lean_closure_set(v___f_1934_, 4, v___x_1931_);
lean_closure_set(v___f_1934_, 5, v_env_1889_);
lean_closure_set(v___f_1934_, 6, v___y_1881_);
lean_closure_set(v___f_1934_, 7, v___x_1909_);
lean_closure_set(v___f_1934_, 8, v_a_1823_);
lean_closure_set(v___f_1934_, 9, v_opts_1912_);
lean_closure_set(v___f_1934_, 10, v___x_1928_);
lean_closure_set(v___f_1934_, 11, v_pos_1837_);
lean_closure_set(v___f_1934_, 12, v___x_1932_);
lean_closure_set(v___f_1934_, 13, v___y_1880_);
lean_closure_set(v___f_1934_, 14, v___y_1877_);
lean_closure_set(v___f_1934_, 15, v___y_1876_);
lean_closure_set(v___f_1934_, 16, v___y_1875_);
lean_closure_set(v___f_1934_, 17, v___x_1933_);
v___x_1935_ = lean_io_bind_task(v___x_1929_, v___f_1934_, v___y_1900_, v_val_1822_);
v___y_1847_ = v___y_1897_;
v___y_1848_ = v___y_1901_;
v___y_1849_ = v___y_1887_;
v___y_1850_ = v___y_1886_;
v___y_1851_ = v___y_1888_;
v_snapshotTasks_1852_ = v_snapshotTasks_1894_;
v_traceTask_1853_ = v___x_1935_;
goto v___jp_1846_;
}
}
}
v___jp_1936_:
{
lean_object* v_env_1960_; lean_object* v_messages_1961_; lean_object* v_scopes_1962_; lean_object* v_infoState_1963_; lean_object* v_traceState_1964_; lean_object* v_snapshotTasks_1965_; 
v_env_1960_ = lean_ctor_get(v___y_1951_, 0);
lean_inc_ref(v_env_1960_);
v_messages_1961_ = lean_ctor_get(v___y_1951_, 1);
lean_inc_ref(v_messages_1961_);
v_scopes_1962_ = lean_ctor_get(v___y_1951_, 2);
lean_inc(v_scopes_1962_);
v_infoState_1963_ = lean_ctor_get(v___y_1951_, 8);
lean_inc_ref(v_infoState_1963_);
v_traceState_1964_ = lean_ctor_get(v___y_1951_, 9);
lean_inc_ref(v_traceState_1964_);
v_snapshotTasks_1965_ = lean_ctor_get(v___y_1951_, 10);
lean_inc_ref(v_snapshotTasks_1965_);
v___y_1874_ = v___y_1937_;
v___y_1875_ = v___y_1938_;
v___y_1876_ = v___y_1939_;
v___y_1877_ = v___y_1942_;
v___y_1878_ = v___y_1941_;
v___y_1879_ = v___y_1940_;
v___y_1880_ = v___y_1944_;
v___y_1881_ = v___y_1943_;
v___y_1882_ = v___y_1945_;
v___y_1883_ = v___y_1946_;
v___y_1884_ = v___y_1947_;
v___y_1885_ = v___y_1948_;
v___y_1886_ = v___y_1949_;
v___y_1887_ = v___y_1950_;
v___y_1888_ = v___y_1951_;
v_env_1889_ = v_env_1960_;
v_messages_1890_ = v_messages_1961_;
v_scopes_1891_ = v_scopes_1962_;
v_infoState_1892_ = v_infoState_1963_;
v_traceState_1893_ = v_traceState_1964_;
v_snapshotTasks_1894_ = v_snapshotTasks_1965_;
v___y_1895_ = v___y_1952_;
v___y_1896_ = v___y_1953_;
v___y_1897_ = v___y_1954_;
v___y_1898_ = v___y_1955_;
v___y_1899_ = v___y_1956_;
v___y_1900_ = v___y_1957_;
v___y_1901_ = v___y_1958_;
v_reportedCmdState_1902_ = v_reportedCmdState_1959_;
goto v___jp_1873_;
}
v___jp_1966_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___f_1995_; uint8_t v___x_1996_; 
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1990_);
lean_ctor_set(v___x_1991_, 1, v_val_1828_);
lean_inc(v___y_1980_);
lean_inc_n(v_pos_1837_, 2);
lean_inc(v_fst_1838_);
v___x_1992_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1838_, v_cmdState_1839_, v_pos_1837_, v___x_1991_, v___y_1980_, v_a_1823_);
v___x_1993_ = lean_box(v_val_1822_);
v___x_1994_ = lean_box(v___x_1826_);
lean_inc_ref(v_a_1823_);
lean_inc(v___y_1972_);
lean_inc_ref(v___x_1833_);
lean_inc_ref(v___x_1992_);
lean_inc_ref(v___y_1973_);
lean_inc_ref(v___y_1974_);
v___f_1995_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1995_, 0, v___y_1974_);
lean_closure_set(v___f_1995_, 1, v___y_1973_);
lean_closure_set(v___f_1995_, 2, v___x_1993_);
lean_closure_set(v___f_1995_, 3, v_val_1830_);
lean_closure_set(v___f_1995_, 4, v___x_1992_);
lean_closure_set(v___f_1995_, 5, v___x_1833_);
lean_closure_set(v___f_1995_, 6, v___y_1972_);
lean_closure_set(v___f_1995_, 7, v___x_1994_);
lean_closure_set(v___f_1995_, 8, v_a_1823_);
lean_closure_set(v___f_1995_, 9, v_pos_1837_);
v___x_1996_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1840_, v___x_1841_);
if (v___x_1996_ == 0)
{
lean_dec(v___y_1977_);
lean_dec(v_fst_1838_);
lean_inc_ref(v___x_1992_);
v___y_1937_ = v___y_1967_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1972_;
v___y_1942_ = v___y_1970_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1982_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___x_1992_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___f_1995_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v_reportedCmdState_1959_ = v___x_1992_;
goto v___jp_1936_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Parser_isTerminalCommand(v_fst_1838_);
if (v___x_1997_ == 0)
{
if (v___x_1996_ == 0)
{
lean_dec(v___y_1977_);
lean_inc_ref(v___x_1992_);
v___y_1937_ = v___y_1967_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1972_;
v___y_1942_ = v___y_1970_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1982_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___x_1992_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___f_1995_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v_reportedCmdState_1959_ = v___x_1992_;
goto v___jp_1936_;
}
else
{
lean_object* v_env_1998_; lean_object* v_messages_1999_; lean_object* v_scopes_2000_; lean_object* v_infoState_2001_; lean_object* v_traceState_2002_; lean_object* v_snapshotTasks_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_env_1998_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_ref_n(v_env_1998_, 2);
v_messages_1999_ = lean_ctor_get(v___x_1992_, 1);
lean_inc_ref(v_messages_1999_);
v_scopes_2000_ = lean_ctor_get(v___x_1992_, 2);
lean_inc(v_scopes_2000_);
v_infoState_2001_ = lean_ctor_get(v___x_1992_, 8);
lean_inc_ref(v_infoState_2001_);
v_traceState_2002_ = lean_ctor_get(v___x_1992_, 9);
lean_inc_ref(v_traceState_2002_);
v_snapshotTasks_2003_ = lean_ctor_get(v___x_1992_, 10);
lean_inc_ref(v_snapshotTasks_2003_);
v___x_2004_ = lean_mk_empty_array_with_capacity(v___y_1977_);
lean_dec(v___y_1977_);
lean_inc_ref(v___x_2004_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_inc_n(v___y_1988_, 3);
v___x_2006_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
lean_ctor_set(v___x_2006_, 2, v___y_1988_);
lean_ctor_set(v___x_2006_, 3, v___y_1988_);
lean_ctor_set_usize(v___x_2006_, 4, v___y_1978_);
v___x_2007_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2006_, 2);
v___x_2008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2006_);
lean_ctor_set(v___x_2008_, 2, v___x_2007_);
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2010_ = l_Lean_Options_empty;
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_mk_empty_array_with_capacity(v___y_1988_);
lean_inc_ref_n(v___x_2012_, 2);
lean_inc_n(v___x_1825_, 2);
v___x_2013_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2013_, 0, v___x_2009_);
lean_ctor_set(v___x_2013_, 1, v___x_2010_);
lean_ctor_set(v___x_2013_, 2, v___x_1825_);
lean_ctor_set(v___x_2013_, 3, v___x_2011_);
lean_ctor_set(v___x_2013_, 4, v___x_2011_);
lean_ctor_set(v___x_2013_, 5, v___x_2012_);
lean_ctor_set(v___x_2013_, 6, v___x_2012_);
lean_ctor_set(v___x_2013_, 7, v___x_2011_);
lean_ctor_set(v___x_2013_, 8, v___x_2011_);
lean_ctor_set(v___x_2013_, 9, v___x_2011_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*10, v_val_1822_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*10 + 1, v_val_1822_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*10 + 2, v_val_1822_);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2011_);
v___x_2015_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2017_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1825_);
v___x_2018_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2019_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
lean_ctor_set(v___x_2019_, 2, v___x_2006_);
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*3, v___x_1826_);
lean_inc_ref(v___y_1989_);
v___x_2020_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2020_, 0, v_env_1998_);
lean_ctor_set(v___x_2020_, 1, v___x_2008_);
lean_ctor_set(v___x_2020_, 2, v___x_2014_);
lean_ctor_set(v___x_2020_, 3, v___x_2007_);
lean_ctor_set(v___x_2020_, 4, v___x_2015_);
lean_ctor_set(v___x_2020_, 5, v___y_1988_);
lean_ctor_set(v___x_2020_, 6, v___x_2016_);
lean_ctor_set(v___x_2020_, 7, v___x_2017_);
lean_ctor_set(v___x_2020_, 8, v___x_2019_);
lean_ctor_set(v___x_2020_, 9, v___y_1989_);
lean_ctor_set(v___x_2020_, 10, v___x_2012_);
v___y_1874_ = v___y_1967_;
v___y_1875_ = v___y_1968_;
v___y_1876_ = v___y_1969_;
v___y_1877_ = v___y_1970_;
v___y_1878_ = v___y_1972_;
v___y_1879_ = v___y_1971_;
v___y_1880_ = v___y_1974_;
v___y_1881_ = v___y_1973_;
v___y_1882_ = v___y_1975_;
v___y_1883_ = v___y_1976_;
v___y_1884_ = v___y_1979_;
v___y_1885_ = v___y_1982_;
v___y_1886_ = v___y_1981_;
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___x_1992_;
v_env_1889_ = v_env_1998_;
v_messages_1890_ = v_messages_1999_;
v_scopes_1891_ = v_scopes_2000_;
v_infoState_1892_ = v_infoState_2001_;
v_traceState_1893_ = v_traceState_2002_;
v_snapshotTasks_1894_ = v_snapshotTasks_2003_;
v___y_1895_ = v___y_1983_;
v___y_1896_ = v___y_1984_;
v___y_1897_ = v___y_1985_;
v___y_1898_ = v___y_1986_;
v___y_1899_ = v___f_1995_;
v___y_1900_ = v___y_1988_;
v___y_1901_ = v___y_1987_;
v_reportedCmdState_1902_ = v___x_2020_;
goto v___jp_1873_;
}
}
else
{
lean_dec(v___y_1977_);
lean_inc_ref(v___x_1992_);
v___y_1937_ = v___y_1967_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1972_;
v___y_1942_ = v___y_1970_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1982_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___x_1992_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___y_1986_;
v___y_1956_ = v___f_1995_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v_reportedCmdState_1959_ = v___x_1992_;
goto v___jp_1936_;
}
}
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2023_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1824_);
v___x_2024_ = l_IO_CancelToken_new();
v___x_2025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1825_);
v___x_2026_ = l_Lean_Name_str___override(v___x_1825_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2028_ = l_Lean_Name_str___override(v___x_2026_, v___x_2027_);
v___x_2029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2030_ = l_Lean_Name_str___override(v___x_2028_, v___x_2029_);
v___x_2031_ = l_Lean_Name_str___override(v___x_2030_, v___x_2027_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = l_Lean_Name_num___override(v___x_2031_, v___x_2032_);
v___x_2034_ = l_Lean_Name_str___override(v___x_2033_, v___x_2027_);
v___x_2035_ = l_Lean_Name_str___override(v___x_2034_, v___x_2029_);
v___x_2036_ = l_Lean_Name_str___override(v___x_2035_, v___x_2027_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2038_ = l_Lean_Name_str___override(v___x_2036_, v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2040_ = l_Lean_Name_str___override(v___x_2038_, v___x_2039_);
v___x_2041_ = l_Lean_Name_toString(v___x_2040_, v___x_1826_);
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_unsigned_to_nat(32u);
v___x_2044_ = ((size_t)5ULL);
v___x_2045_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2041_, 2);
v___x_2046_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2023_);
lean_ctor_set(v___x_2046_, 2, v___x_2042_);
lean_ctor_set(v___x_2046_, 3, v___x_2045_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*4, v_val_1822_);
v___x_2047_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2048_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2048_, 0, v___x_2041_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_ctor_set(v___x_2048_, 2, v___x_2042_);
lean_ctor_set(v___x_2048_, 3, v___x_2045_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*4, v_val_1822_);
lean_inc(v_fst_1827_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_fst_1827_);
v___x_2050_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2049_);
lean_inc(v___x_2024_);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2024_);
v___x_2052_ = l_IO_Promise_result_x21___redArg(v_val_1828_);
lean_inc_ref(v___x_2052_);
lean_inc(v___x_2050_);
lean_inc_ref_n(v___x_2049_, 3);
v___x_2053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2049_);
lean_ctor_set(v___x_2053_, 1, v___x_2050_);
lean_ctor_set(v___x_2053_, 2, v___x_2051_);
lean_ctor_set(v___x_2053_, 3, v___x_2052_);
v___x_2054_ = l_IO_Promise_result_x21___redArg(v_val_1829_);
lean_inc_ref(v___x_2054_);
lean_inc_n(v___x_1819_, 3);
v___x_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2049_);
lean_ctor_set(v___x_2055_, 1, v___x_1819_);
lean_ctor_set(v___x_2055_, 2, v___x_2042_);
lean_ctor_set(v___x_2055_, 3, v___x_2054_);
v___x_2056_ = l_IO_Promise_result_x21___redArg(v_val_1830_);
lean_inc_ref(v___x_2056_);
v___x_2057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2049_);
lean_ctor_set(v___x_2057_, 1, v___x_1819_);
lean_ctor_set(v___x_2057_, 2, v___x_2042_);
lean_ctor_set(v___x_2057_, 3, v___x_2056_);
v___x_2058_ = l_IO_Promise_result_x21___redArg(v_val_1820_);
v___x_2059_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2042_);
lean_ctor_set(v___x_2059_, 1, v___x_1819_);
lean_ctor_set(v___x_2059_, 2, v___x_2042_);
lean_ctor_set(v___x_2059_, 3, v___x_2058_);
lean_inc_ref(v___x_2048_);
v___x_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2048_);
lean_ctor_set(v___x_2060_, 1, v___x_2053_);
lean_ctor_set(v___x_2060_, 2, v___x_2055_);
lean_ctor_set(v___x_2060_, 3, v___x_2057_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2046_);
lean_ctor_set(v___x_2061_, 1, v_fst_1827_);
lean_ctor_set(v___x_2061_, 2, v_snd_1831_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
lean_ctor_set(v___x_2061_, 4, v___y_2022_);
v___x_2062_ = lean_io_promise_resolve(v___x_2061_, v_prom_1832_);
if (lean_obj_tag(v_old_x3f_1842_) == 0)
{
lean_inc_ref(v___x_2041_);
lean_inc_ref(v___x_2048_);
v___y_1967_ = v___x_2044_;
v___y_1968_ = v___x_2042_;
v___y_1969_ = v___x_2048_;
v___y_1970_ = v___x_2042_;
v___y_1971_ = v___x_2043_;
v___y_1972_ = v___x_2032_;
v___y_1973_ = v___x_2045_;
v___y_1974_ = v___x_2041_;
v___y_1975_ = v___x_2056_;
v___y_1976_ = v___x_2054_;
v___y_1977_ = v___x_2043_;
v___y_1978_ = v___x_2044_;
v___y_1979_ = v___x_2049_;
v___y_1980_ = v___x_2024_;
v___y_1981_ = v___x_2042_;
v___y_1982_ = v___x_2041_;
v___y_1983_ = v___x_2042_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2042_;
v___y_1986_ = v___x_2050_;
v___y_1987_ = v___x_2048_;
v___y_1988_ = v___x_2032_;
v___y_1989_ = v___x_2045_;
v___y_1990_ = v___x_2042_;
goto v___jp_1966_;
}
else
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_val_2063_ = lean_ctor_get(v_old_x3f_1842_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_old_x3f_1842_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2065_ = v_old_x3f_1842_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_old_x3f_1842_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_elabSnap_2067_; lean_object* v_stx_2068_; lean_object* v_elabSnap_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v_elabSnap_2067_ = lean_ctor_get(v_val_2063_, 3);
lean_inc_ref(v_elabSnap_2067_);
v_stx_2068_ = lean_ctor_get(v_val_2063_, 1);
lean_inc(v_stx_2068_);
lean_dec(v_val_2063_);
v_elabSnap_2069_ = lean_ctor_get(v_elabSnap_2067_, 1);
lean_inc_ref(v_elabSnap_2069_);
lean_dec_ref(v_elabSnap_2067_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_stx_2068_);
lean_ctor_set(v___x_2070_, 1, v_elabSnap_2069_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2070_);
v___x_2072_ = v___x_2065_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_inc_ref(v___x_2041_);
lean_inc_ref(v___x_2048_);
v___y_1967_ = v___x_2044_;
v___y_1968_ = v___x_2042_;
v___y_1969_ = v___x_2048_;
v___y_1970_ = v___x_2042_;
v___y_1971_ = v___x_2043_;
v___y_1972_ = v___x_2032_;
v___y_1973_ = v___x_2045_;
v___y_1974_ = v___x_2041_;
v___y_1975_ = v___x_2056_;
v___y_1976_ = v___x_2054_;
v___y_1977_ = v___x_2043_;
v___y_1978_ = v___x_2044_;
v___y_1979_ = v___x_2049_;
v___y_1980_ = v___x_2024_;
v___y_1981_ = v___x_2042_;
v___y_1982_ = v___x_2041_;
v___y_1983_ = v___x_2042_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2042_;
v___y_1986_ = v___x_2050_;
v___y_1987_ = v___x_2048_;
v___y_1988_ = v___x_2032_;
v___y_1989_ = v___x_2045_;
v___y_1990_ = v___x_2072_;
goto v___jp_1966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2087_, uint8_t v_val_2088_, lean_object* v_a_2089_, lean_object* v_snd_2090_, lean_object* v___x_2091_, uint8_t v___x_2092_, lean_object* v_prom_2093_, lean_object* v___x_2094_, lean_object* v___f_2095_, lean_object* v___f_2096_, lean_object* v___f_2097_, lean_object* v_pos_2098_, lean_object* v_fst_2099_, lean_object* v_cmdState_2100_, lean_object* v_opts_2101_, lean_object* v_old_x3f_2102_, lean_object* v_parseCancelTk_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v_snapshotTasks_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v_traceTask_2118_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; size_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v_env_2159_; lean_object* v_messages_2160_; lean_object* v_scopes_2161_; lean_object* v_infoState_2162_; lean_object* v_traceState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v_reportedCmdState_2171_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; size_t v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v_reportedCmdState_2230_; lean_object* v___x_2237_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; size_t v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; size_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v_fst_2374_; lean_object* v_snd_2375_; uint8_t v___y_2388_; uint8_t v___x_2391_; 
v___x_2105_ = lean_io_promise_new();
v___x_2106_ = lean_io_promise_new();
v___x_2107_ = lean_io_promise_new();
v___x_2108_ = lean_io_promise_new();
v___x_2237_ = l_Lean_internal_cmdlineSnapshots;
v___x_2391_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2101_, v___x_2237_);
if (v___x_2391_ == 0)
{
v___y_2388_ = v___x_2391_;
goto v___jp_2387_;
}
else
{
uint8_t v___x_2392_; 
lean_inc(v_fst_2099_);
v___x_2392_ = l_Lean_Parser_isTerminalCommand(v_fst_2099_);
if (v___x_2392_ == 0)
{
v___y_2388_ = v___x_2391_;
goto v___jp_2387_;
}
else
{
lean_inc_ref(v_fst_2087_);
lean_inc(v_fst_2099_);
v_fst_2374_ = v_fst_2099_;
v_snd_2375_ = v_fst_2087_;
goto v___jp_2373_;
}
}
v___jp_2109_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2119_, 0, v___y_2110_);
lean_ctor_set(v___x_2119_, 1, v___y_2115_);
lean_ctor_set(v___x_2119_, 2, v___y_2116_);
lean_ctor_set(v___x_2119_, 3, v_traceTask_2118_);
v___x_2120_ = lean_array_push(v_snapshotTasks_2113_, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___y_2117_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_io_promise_resolve(v___x_2121_, v___x_2108_);
lean_dec(v___x_2108_);
if (lean_obj_tag(v___y_2111_) == 1)
{
lean_object* v_val_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_val_2123_ = lean_ctor_get(v___y_2111_, 0);
lean_inc(v_val_2123_);
lean_dec_ref(v___y_2111_);
v___x_2124_ = lean_box(0);
v___x_2125_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2124_, v_fst_2087_, v___y_2112_, v_val_2123_, v_val_2088_, v___y_2114_, v_a_2089_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; 
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v_fst_2087_);
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
}
v___jp_2127_:
{
lean_object* v_snapshotTasks_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_snapshotTasks_2136_ = lean_ctor_get(v___y_2129_, 10);
lean_inc_ref(v_snapshotTasks_2136_);
v___x_2137_ = lean_mk_empty_array_with_capacity(v___y_2135_);
lean_dec(v___y_2135_);
lean_inc_ref(v___y_2134_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___y_2134_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_task_pure(v___x_2138_);
v___y_2110_ = v___y_2128_;
v___y_2111_ = v___y_2130_;
v___y_2112_ = v___y_2129_;
v_snapshotTasks_2113_ = v_snapshotTasks_2136_;
v___y_2114_ = v___y_2131_;
v___y_2115_ = v___y_2132_;
v___y_2116_ = v___y_2133_;
v___y_2117_ = v___y_2134_;
v_traceTask_2118_ = v___x_2139_;
goto v___jp_2109_;
}
v___jp_2140_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_opts_2181_; uint8_t v_hasTrace_2182_; 
v___x_2172_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2160_);
v___x_2173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2173_, 0, v___y_2153_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
lean_ctor_set(v___x_2173_, 2, v___y_2165_);
lean_ctor_set(v___x_2173_, 3, v_traceState_2163_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*4, v_val_2088_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_reportedCmdState_2171_);
v___x_2175_ = lean_io_promise_resolve(v___x_2174_, v___x_2106_);
lean_dec(v___x_2106_);
v___x_2176_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2162_);
lean_inc(v___y_2169_);
v___x_2177_ = l_BaseIO_chainTask___redArg(v___x_2176_, v___y_2152_, v___y_2169_, v___x_2092_);
v___x_2178_ = l_Lean_inheritedTraceOptions;
v___x_2179_ = lean_st_ref_get(v___x_2178_);
v___x_2180_ = l_List_head_x21___redArg(v___x_2094_, v_scopes_2161_);
lean_dec(v_scopes_2161_);
lean_dec_ref(v___x_2094_);
v_opts_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc_ref(v_opts_2181_);
lean_dec(v___x_2180_);
v_hasTrace_2182_ = lean_ctor_get_uint8(v_opts_2181_, sizeof(void*)*1);
if (v_hasTrace_2182_ == 0)
{
lean_dec_ref(v_opts_2181_);
lean_dec(v___x_2179_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_snapshotTasks_2164_);
lean_dec_ref(v_env_2159_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_pos_2098_);
lean_dec_ref(v___f_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v___f_2095_);
lean_dec(v___x_2091_);
v___y_2128_ = v___y_2149_;
v___y_2129_ = v___y_2158_;
v___y_2130_ = v___y_2150_;
v___y_2131_ = v___y_2154_;
v___y_2132_ = v___y_2156_;
v___y_2133_ = v___y_2167_;
v___y_2134_ = v___y_2168_;
v___y_2135_ = v___y_2169_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2179_, v_opts_2181_, v___x_2183_);
lean_dec(v___x_2179_);
if (v___x_2184_ == 0)
{
lean_dec_ref(v_opts_2181_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_snapshotTasks_2164_);
lean_dec_ref(v_env_2159_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_pos_2098_);
lean_dec_ref(v___f_2097_);
lean_dec_ref(v___f_2096_);
lean_dec_ref(v___f_2095_);
lean_dec(v___x_2091_);
v___y_2128_ = v___y_2149_;
v___y_2129_ = v___y_2158_;
v___y_2130_ = v___y_2150_;
v___y_2131_ = v___y_2154_;
v___y_2132_ = v___y_2156_;
v___y_2133_ = v___y_2167_;
v___y_2134_ = v___y_2168_;
v___y_2135_ = v___y_2169_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
lean_inc_n(v___y_2169_, 3);
v___x_2185_ = lean_task_map(v___f_2095_, v___y_2151_, v___y_2169_, v___x_2092_);
lean_inc_n(v___y_2167_, 3);
lean_inc_n(v___y_2155_, 2);
lean_inc_n(v___y_2170_, 2);
v___x_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2170_);
lean_ctor_set(v___x_2186_, 1, v___y_2155_);
lean_ctor_set(v___x_2186_, 2, v___y_2167_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
v___x_2187_ = lean_task_map(v___f_2096_, v___y_2157_, v___y_2169_, v___x_2092_);
v___x_2188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2170_);
lean_ctor_set(v___x_2188_, 1, v___y_2155_);
lean_ctor_set(v___x_2188_, 2, v___y_2167_);
lean_ctor_set(v___x_2188_, 3, v___x_2187_);
v___x_2189_ = lean_task_map(v___f_2097_, v___y_2166_, v___y_2169_, v___x_2092_);
v___x_2190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2190_, 0, v___y_2170_);
lean_ctor_set(v___x_2190_, 1, v___y_2155_);
lean_ctor_set(v___x_2190_, 2, v___y_2167_);
lean_ctor_set(v___x_2190_, 3, v___x_2189_);
v___x_2191_ = lean_unsigned_to_nat(3u);
v___x_2192_ = lean_mk_empty_array_with_capacity(v___x_2191_);
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2186_);
v___x_2194_ = lean_array_push(v___x_2193_, v___x_2188_);
v___x_2195_ = lean_array_push(v___x_2194_, v___x_2190_);
v___x_2196_ = l_Array_append___redArg(v___x_2195_, v_snapshotTasks_2164_);
lean_inc_ref(v___y_2168_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2168_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
lean_inc_ref(v___x_2197_);
v___x_2198_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2197_);
v___x_2199_ = lean_box_usize(v___y_2148_);
v___x_2200_ = lean_box(v___x_2092_);
v___x_2201_ = lean_box(v_val_2088_);
v___x_2202_ = lean_box(v___x_2184_);
lean_inc_ref(v_a_2089_);
lean_inc_ref(v___y_2141_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2203_, 0, v___x_2091_);
lean_closure_set(v___f_2203_, 1, v___y_2144_);
lean_closure_set(v___f_2203_, 2, v___y_2147_);
lean_closure_set(v___f_2203_, 3, v___x_2199_);
lean_closure_set(v___f_2203_, 4, v___x_2200_);
lean_closure_set(v___f_2203_, 5, v_env_2159_);
lean_closure_set(v___f_2203_, 6, v___y_2141_);
lean_closure_set(v___f_2203_, 7, v___x_2178_);
lean_closure_set(v___f_2203_, 8, v_a_2089_);
lean_closure_set(v___f_2203_, 9, v_opts_2181_);
lean_closure_set(v___f_2203_, 10, v___x_2197_);
lean_closure_set(v___f_2203_, 11, v_pos_2098_);
lean_closure_set(v___f_2203_, 12, v___x_2201_);
lean_closure_set(v___f_2203_, 13, v___y_2143_);
lean_closure_set(v___f_2203_, 14, v___y_2146_);
lean_closure_set(v___f_2203_, 15, v___y_2142_);
lean_closure_set(v___f_2203_, 16, v___y_2145_);
lean_closure_set(v___f_2203_, 17, v___x_2202_);
v___x_2204_ = lean_io_bind_task(v___x_2198_, v___f_2203_, v___y_2169_, v_val_2088_);
v___y_2110_ = v___y_2149_;
v___y_2111_ = v___y_2150_;
v___y_2112_ = v___y_2158_;
v_snapshotTasks_2113_ = v_snapshotTasks_2164_;
v___y_2114_ = v___y_2154_;
v___y_2115_ = v___y_2156_;
v___y_2116_ = v___y_2167_;
v___y_2117_ = v___y_2168_;
v_traceTask_2118_ = v___x_2204_;
goto v___jp_2109_;
}
}
}
v___jp_2205_:
{
lean_object* v_env_2231_; lean_object* v_messages_2232_; lean_object* v_scopes_2233_; lean_object* v_infoState_2234_; lean_object* v_traceState_2235_; lean_object* v_snapshotTasks_2236_; 
v_env_2231_ = lean_ctor_get(v___y_2223_, 0);
lean_inc_ref(v_env_2231_);
v_messages_2232_ = lean_ctor_get(v___y_2223_, 1);
lean_inc_ref(v_messages_2232_);
v_scopes_2233_ = lean_ctor_get(v___y_2223_, 2);
lean_inc(v_scopes_2233_);
v_infoState_2234_ = lean_ctor_get(v___y_2223_, 8);
lean_inc_ref(v_infoState_2234_);
v_traceState_2235_ = lean_ctor_get(v___y_2223_, 9);
lean_inc_ref(v_traceState_2235_);
v_snapshotTasks_2236_ = lean_ctor_get(v___y_2223_, 10);
lean_inc_ref(v_snapshotTasks_2236_);
v___y_2141_ = v___y_2206_;
v___y_2142_ = v___y_2208_;
v___y_2143_ = v___y_2207_;
v___y_2144_ = v___y_2209_;
v___y_2145_ = v___y_2210_;
v___y_2146_ = v___y_2212_;
v___y_2147_ = v___y_2211_;
v___y_2148_ = v___y_2213_;
v___y_2149_ = v___y_2214_;
v___y_2150_ = v___y_2215_;
v___y_2151_ = v___y_2216_;
v___y_2152_ = v___y_2217_;
v___y_2153_ = v___y_2218_;
v___y_2154_ = v___y_2219_;
v___y_2155_ = v___y_2220_;
v___y_2156_ = v___y_2221_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2223_;
v_env_2159_ = v_env_2231_;
v_messages_2160_ = v_messages_2232_;
v_scopes_2161_ = v_scopes_2233_;
v_infoState_2162_ = v_infoState_2234_;
v_traceState_2163_ = v_traceState_2235_;
v_snapshotTasks_2164_ = v_snapshotTasks_2236_;
v___y_2165_ = v___y_2224_;
v___y_2166_ = v___y_2225_;
v___y_2167_ = v___y_2226_;
v___y_2168_ = v___y_2227_;
v___y_2169_ = v___y_2228_;
v___y_2170_ = v___y_2229_;
v_reportedCmdState_2171_ = v_reportedCmdState_2230_;
goto v___jp_2140_;
}
v___jp_2238_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; uint8_t v___x_2270_; 
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___y_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2105_);
lean_inc(v___y_2251_);
lean_inc_n(v_pos_2098_, 2);
lean_inc(v_fst_2099_);
v___x_2266_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2099_, v_cmdState_2100_, v_pos_2098_, v___x_2265_, v___y_2251_, v_a_2089_);
v___x_2267_ = lean_box(v_val_2088_);
v___x_2268_ = lean_box(v___x_2092_);
lean_inc_ref(v_a_2089_);
lean_inc(v___y_2245_);
lean_inc_ref(v___x_2094_);
lean_inc_ref(v___x_2266_);
lean_inc_ref(v___y_2239_);
lean_inc_ref(v___y_2241_);
v___f_2269_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2269_, 0, v___y_2241_);
lean_closure_set(v___f_2269_, 1, v___y_2239_);
lean_closure_set(v___f_2269_, 2, v___x_2267_);
lean_closure_set(v___f_2269_, 3, v___x_2107_);
lean_closure_set(v___f_2269_, 4, v___x_2266_);
lean_closure_set(v___f_2269_, 5, v___x_2094_);
lean_closure_set(v___f_2269_, 6, v___y_2245_);
lean_closure_set(v___f_2269_, 7, v___x_2268_);
lean_closure_set(v___f_2269_, 8, v_a_2089_);
lean_closure_set(v___f_2269_, 9, v_pos_2098_);
v___x_2270_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2101_, v___x_2237_);
if (v___x_2270_ == 0)
{
lean_dec(v___y_2262_);
lean_dec(v_fst_2099_);
lean_inc_ref(v___x_2266_);
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2269_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2251_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2252_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___x_2266_;
v___y_2224_ = v___y_2256_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v_reportedCmdState_2230_ = v___x_2266_;
goto v___jp_2205_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Parser_isTerminalCommand(v_fst_2099_);
if (v___x_2271_ == 0)
{
if (v___x_2270_ == 0)
{
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2266_);
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2269_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2251_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2252_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___x_2266_;
v___y_2224_ = v___y_2256_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v_reportedCmdState_2230_ = v___x_2266_;
goto v___jp_2205_;
}
else
{
lean_object* v_env_2272_; lean_object* v_messages_2273_; lean_object* v_scopes_2274_; lean_object* v_infoState_2275_; lean_object* v_traceState_2276_; lean_object* v_snapshotTasks_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_env_2272_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_ref_n(v_env_2272_, 2);
v_messages_2273_ = lean_ctor_get(v___x_2266_, 1);
lean_inc_ref(v_messages_2273_);
v_scopes_2274_ = lean_ctor_get(v___x_2266_, 2);
lean_inc(v_scopes_2274_);
v_infoState_2275_ = lean_ctor_get(v___x_2266_, 8);
lean_inc_ref(v_infoState_2275_);
v_traceState_2276_ = lean_ctor_get(v___x_2266_, 9);
lean_inc_ref(v_traceState_2276_);
v_snapshotTasks_2277_ = lean_ctor_get(v___x_2266_, 10);
lean_inc_ref(v_snapshotTasks_2277_);
v___x_2278_ = lean_mk_empty_array_with_capacity(v___y_2262_);
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2278_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_inc_n(v___y_2261_, 3);
v___x_2280_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2278_);
lean_ctor_set(v___x_2280_, 2, v___y_2261_);
lean_ctor_set(v___x_2280_, 3, v___y_2261_);
lean_ctor_set_usize(v___x_2280_, 4, v___y_2258_);
v___x_2281_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2280_, 2);
v___x_2282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2280_);
lean_ctor_set(v___x_2282_, 2, v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2284_ = l_Lean_Options_empty;
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_mk_empty_array_with_capacity(v___y_2261_);
lean_inc_ref_n(v___x_2286_, 2);
lean_inc_n(v___x_2091_, 2);
v___x_2287_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2287_, 0, v___x_2283_);
lean_ctor_set(v___x_2287_, 1, v___x_2284_);
lean_ctor_set(v___x_2287_, 2, v___x_2091_);
lean_ctor_set(v___x_2287_, 3, v___x_2285_);
lean_ctor_set(v___x_2287_, 4, v___x_2285_);
lean_ctor_set(v___x_2287_, 5, v___x_2286_);
lean_ctor_set(v___x_2287_, 6, v___x_2286_);
lean_ctor_set(v___x_2287_, 7, v___x_2285_);
lean_ctor_set(v___x_2287_, 8, v___x_2285_);
lean_ctor_set(v___x_2287_, 9, v___x_2285_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*10, v_val_2088_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*10 + 1, v_val_2088_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*10 + 2, v_val_2088_);
v___x_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2285_);
v___x_2289_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2291_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2091_);
v___x_2292_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2293_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_ctor_set(v___x_2293_, 2, v___x_2280_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*3, v___x_2092_);
lean_inc_ref(v___y_2254_);
v___x_2294_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2294_, 0, v_env_2272_);
lean_ctor_set(v___x_2294_, 1, v___x_2282_);
lean_ctor_set(v___x_2294_, 2, v___x_2288_);
lean_ctor_set(v___x_2294_, 3, v___x_2281_);
lean_ctor_set(v___x_2294_, 4, v___x_2289_);
lean_ctor_set(v___x_2294_, 5, v___y_2261_);
lean_ctor_set(v___x_2294_, 6, v___x_2290_);
lean_ctor_set(v___x_2294_, 7, v___x_2291_);
lean_ctor_set(v___x_2294_, 8, v___x_2293_);
lean_ctor_set(v___x_2294_, 9, v___y_2254_);
lean_ctor_set(v___x_2294_, 10, v___x_2286_);
v___y_2141_ = v___y_2239_;
v___y_2142_ = v___y_2240_;
v___y_2143_ = v___y_2241_;
v___y_2144_ = v___y_2242_;
v___y_2145_ = v___y_2243_;
v___y_2146_ = v___y_2244_;
v___y_2147_ = v___y_2245_;
v___y_2148_ = v___y_2246_;
v___y_2149_ = v___y_2247_;
v___y_2150_ = v___y_2248_;
v___y_2151_ = v___y_2249_;
v___y_2152_ = v___f_2269_;
v___y_2153_ = v___y_2250_;
v___y_2154_ = v___y_2251_;
v___y_2155_ = v___y_2253_;
v___y_2156_ = v___y_2252_;
v___y_2157_ = v___y_2255_;
v___y_2158_ = v___x_2266_;
v_env_2159_ = v_env_2272_;
v_messages_2160_ = v_messages_2273_;
v_scopes_2161_ = v_scopes_2274_;
v_infoState_2162_ = v_infoState_2275_;
v_traceState_2163_ = v_traceState_2276_;
v_snapshotTasks_2164_ = v_snapshotTasks_2277_;
v___y_2165_ = v___y_2256_;
v___y_2166_ = v___y_2257_;
v___y_2167_ = v___y_2259_;
v___y_2168_ = v___y_2260_;
v___y_2169_ = v___y_2261_;
v___y_2170_ = v___y_2263_;
v_reportedCmdState_2171_ = v___x_2294_;
goto v___jp_2140_;
}
}
else
{
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2266_);
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2269_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2251_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2252_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___x_2266_;
v___y_2224_ = v___y_2256_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v_reportedCmdState_2230_ = v___x_2266_;
goto v___jp_2205_;
}
}
}
v___jp_2295_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2301_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2090_);
v___x_2302_ = l_IO_CancelToken_new();
v___x_2303_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2091_);
v___x_2304_ = l_Lean_Name_str___override(v___x_2091_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2306_ = l_Lean_Name_str___override(v___x_2304_, v___x_2305_);
v___x_2307_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2308_ = l_Lean_Name_str___override(v___x_2306_, v___x_2307_);
v___x_2309_ = l_Lean_Name_str___override(v___x_2308_, v___x_2305_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_Lean_Name_num___override(v___x_2309_, v___x_2310_);
v___x_2312_ = l_Lean_Name_str___override(v___x_2311_, v___x_2305_);
v___x_2313_ = l_Lean_Name_str___override(v___x_2312_, v___x_2307_);
v___x_2314_ = l_Lean_Name_str___override(v___x_2313_, v___x_2305_);
v___x_2315_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2316_ = l_Lean_Name_str___override(v___x_2314_, v___x_2315_);
v___x_2317_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2318_ = l_Lean_Name_str___override(v___x_2316_, v___x_2317_);
v___x_2319_ = l_Lean_Name_toString(v___x_2318_, v___x_2092_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_unsigned_to_nat(32u);
v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
lean_dec_ref(v___x_2322_);
v___x_2323_ = ((size_t)5ULL);
v___x_2324_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2319_, 2);
v___x_2325_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2319_);
lean_ctor_set(v___x_2325_, 1, v___x_2301_);
lean_ctor_set(v___x_2325_, 2, v___x_2320_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*4, v_val_2088_);
v___x_2326_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2327_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2327_, 0, v___x_2319_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_ctor_set(v___x_2327_, 2, v___x_2320_);
lean_ctor_set(v___x_2327_, 3, v___x_2324_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*4, v_val_2088_);
lean_inc(v___y_2297_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___y_2297_);
v___x_2329_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2328_);
lean_inc(v___x_2302_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2302_);
v___x_2331_ = l_IO_Promise_result_x21___redArg(v___x_2105_);
lean_inc_ref(v___x_2331_);
lean_inc(v___x_2329_);
lean_inc_ref_n(v___x_2328_, 3);
v___x_2332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2329_);
lean_ctor_set(v___x_2332_, 2, v___x_2330_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
v___x_2333_ = l_IO_Promise_result_x21___redArg(v___x_2106_);
lean_inc_ref(v___x_2333_);
lean_inc_n(v___y_2299_, 3);
v___x_2334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2328_);
lean_ctor_set(v___x_2334_, 1, v___y_2299_);
lean_ctor_set(v___x_2334_, 2, v___x_2320_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
v___x_2335_ = l_IO_Promise_result_x21___redArg(v___x_2107_);
lean_inc_ref(v___x_2335_);
v___x_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2328_);
lean_ctor_set(v___x_2336_, 1, v___y_2299_);
lean_ctor_set(v___x_2336_, 2, v___x_2320_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
v___x_2337_ = l_IO_Promise_result_x21___redArg(v___x_2108_);
v___x_2338_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2320_);
lean_ctor_set(v___x_2338_, 1, v___y_2299_);
lean_ctor_set(v___x_2338_, 2, v___x_2320_);
lean_ctor_set(v___x_2338_, 3, v___x_2337_);
lean_inc_ref(v___x_2327_);
v___x_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2327_);
lean_ctor_set(v___x_2339_, 1, v___x_2332_);
lean_ctor_set(v___x_2339_, 2, v___x_2334_);
lean_ctor_set(v___x_2339_, 3, v___x_2336_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
v___x_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2325_);
lean_ctor_set(v___x_2340_, 1, v___y_2297_);
lean_ctor_set(v___x_2340_, 2, v___y_2298_);
lean_ctor_set(v___x_2340_, 3, v___x_2339_);
lean_ctor_set(v___x_2340_, 4, v___y_2300_);
v___x_2341_ = lean_io_promise_resolve(v___x_2340_, v_prom_2093_);
if (lean_obj_tag(v_old_x3f_2102_) == 0)
{
lean_inc_ref(v___x_2319_);
lean_inc_ref(v___x_2327_);
v___y_2239_ = v___x_2324_;
v___y_2240_ = v___x_2327_;
v___y_2241_ = v___x_2319_;
v___y_2242_ = v___x_2321_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2320_;
v___y_2245_ = v___x_2310_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2320_;
v___y_2248_ = v___y_2296_;
v___y_2249_ = v___x_2331_;
v___y_2250_ = v___x_2319_;
v___y_2251_ = v___x_2302_;
v___y_2252_ = v___y_2299_;
v___y_2253_ = v___x_2329_;
v___y_2254_ = v___x_2324_;
v___y_2255_ = v___x_2333_;
v___y_2256_ = v___x_2320_;
v___y_2257_ = v___x_2335_;
v___y_2258_ = v___x_2323_;
v___y_2259_ = v___x_2320_;
v___y_2260_ = v___x_2327_;
v___y_2261_ = v___x_2310_;
v___y_2262_ = v___x_2321_;
v___y_2263_ = v___x_2328_;
v___y_2264_ = v___x_2320_;
goto v___jp_2238_;
}
else
{
lean_object* v_val_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2353_; 
v_val_2342_ = lean_ctor_get(v_old_x3f_2102_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_old_x3f_2102_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2344_ = v_old_x3f_2102_;
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_val_2342_);
lean_dec(v_old_x3f_2102_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_elabSnap_2346_; lean_object* v_stx_2347_; lean_object* v_elabSnap_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v_elabSnap_2346_ = lean_ctor_get(v_val_2342_, 3);
lean_inc_ref(v_elabSnap_2346_);
v_stx_2347_ = lean_ctor_get(v_val_2342_, 1);
lean_inc(v_stx_2347_);
lean_dec(v_val_2342_);
v_elabSnap_2348_ = lean_ctor_get(v_elabSnap_2346_, 1);
lean_inc_ref(v_elabSnap_2348_);
lean_dec_ref(v_elabSnap_2346_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_stx_2347_);
lean_ctor_set(v___x_2349_, 1, v_elabSnap_2348_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2349_);
v___x_2351_ = v___x_2344_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_inc_ref(v___x_2319_);
lean_inc_ref(v___x_2327_);
v___y_2239_ = v___x_2324_;
v___y_2240_ = v___x_2327_;
v___y_2241_ = v___x_2319_;
v___y_2242_ = v___x_2321_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2320_;
v___y_2245_ = v___x_2310_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2320_;
v___y_2248_ = v___y_2296_;
v___y_2249_ = v___x_2331_;
v___y_2250_ = v___x_2319_;
v___y_2251_ = v___x_2302_;
v___y_2252_ = v___y_2299_;
v___y_2253_ = v___x_2329_;
v___y_2254_ = v___x_2324_;
v___y_2255_ = v___x_2333_;
v___y_2256_ = v___x_2320_;
v___y_2257_ = v___x_2335_;
v___y_2258_ = v___x_2323_;
v___y_2259_ = v___x_2320_;
v___y_2260_ = v___x_2327_;
v___y_2261_ = v___x_2310_;
v___y_2262_ = v___x_2321_;
v___y_2263_ = v___x_2328_;
v___y_2264_ = v___x_2351_;
goto v___jp_2238_;
}
}
}
}
v___jp_2354_:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2357_);
lean_inc(v_fst_2099_);
v___x_2359_ = l_Lean_Parser_isTerminalCommand(v_fst_2099_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v_toProcessingContext_2361_; lean_object* v_pos_2362_; lean_object* v_endPos_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2360_ = lean_io_promise_new();
v_toProcessingContext_2361_ = lean_ctor_get(v_a_2089_, 0);
v_pos_2362_ = lean_ctor_get(v_fst_2087_, 0);
v_endPos_2363_ = lean_ctor_get(v_toProcessingContext_2361_, 3);
lean_inc(v___x_2360_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2360_);
v___x_2365_ = lean_box(0);
lean_inc(v_endPos_2363_);
lean_inc(v_pos_2362_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_pos_2362_);
lean_ctor_set(v___x_2366_, 1, v_endPos_2363_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_parseCancelTk_2103_);
v___x_2369_ = l_IO_Promise_result_x21___redArg(v___x_2360_);
lean_dec(v___x_2360_);
v___x_2370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2365_);
lean_ctor_set(v___x_2370_, 1, v___x_2367_);
lean_ctor_set(v___x_2370_, 2, v___x_2368_);
lean_ctor_set(v___x_2370_, 3, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
v___y_2296_ = v___x_2364_;
v___y_2297_ = v___y_2355_;
v___y_2298_ = v___y_2356_;
v___y_2299_ = v___x_2358_;
v___y_2300_ = v___x_2371_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2372_; 
lean_dec(v_parseCancelTk_2103_);
v___x_2372_ = lean_box(0);
v___y_2296_ = v___x_2372_;
v___y_2297_ = v___y_2355_;
v___y_2298_ = v___y_2356_;
v___y_2299_ = v___x_2358_;
v___y_2300_ = v___x_2372_;
goto v___jp_2295_;
}
}
v___jp_2373_:
{
lean_object* v___x_2376_; 
lean_inc(v_fst_2099_);
v___x_2376_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2099_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_box(0);
v___y_2355_ = v_fst_2374_;
v___y_2356_ = v_snd_2375_;
v___y_2357_ = v___x_2377_;
goto v___jp_2354_;
}
else
{
lean_object* v_val_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_val_2378_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_val_2378_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_inc(v_val_2378_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_val_2378_);
lean_ctor_set(v___x_2382_, 1, v_val_2378_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2355_ = v_fst_2374_;
v___y_2356_ = v_snd_2375_;
v___y_2357_ = v___x_2384_;
goto v___jp_2354_;
}
}
}
}
v___jp_2387_:
{
if (v___y_2388_ == 0)
{
lean_inc_ref(v_fst_2087_);
lean_inc(v_fst_2099_);
v_fst_2374_ = v_fst_2099_;
v_snd_2375_ = v_fst_2087_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2374_ = v___x_2389_;
v_snd_2375_ = v___x_2390_;
goto v___jp_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2393_ = _args[0];
lean_object* v_val_2394_ = _args[1];
lean_object* v_a_2395_ = _args[2];
lean_object* v_snd_2396_ = _args[3];
lean_object* v___x_2397_ = _args[4];
lean_object* v___x_2398_ = _args[5];
lean_object* v_prom_2399_ = _args[6];
lean_object* v___x_2400_ = _args[7];
lean_object* v___f_2401_ = _args[8];
lean_object* v___f_2402_ = _args[9];
lean_object* v___f_2403_ = _args[10];
lean_object* v_pos_2404_ = _args[11];
lean_object* v_fst_2405_ = _args[12];
lean_object* v_cmdState_2406_ = _args[13];
lean_object* v_opts_2407_ = _args[14];
lean_object* v_old_x3f_2408_ = _args[15];
lean_object* v_parseCancelTk_2409_ = _args[16];
lean_object* v___y_2410_ = _args[17];
_start:
{
uint8_t v_val_45714__boxed_2411_; uint8_t v___x_45717__boxed_2412_; lean_object* v_res_2413_; 
v_val_45714__boxed_2411_ = lean_unbox(v_val_2394_);
v___x_45717__boxed_2412_ = lean_unbox(v___x_2398_);
v_res_2413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2393_, v_val_45714__boxed_2411_, v_a_2395_, v_snd_2396_, v___x_2397_, v___x_45717__boxed_2412_, v_prom_2399_, v___x_2400_, v___f_2401_, v___f_2402_, v___f_2403_, v_pos_2404_, v_fst_2405_, v_cmdState_2406_, v_opts_2407_, v_old_x3f_2408_, v_parseCancelTk_2409_);
lean_dec_ref(v_opts_2407_);
lean_dec(v_prom_2399_);
lean_dec_ref(v_a_2395_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2416_, lean_object* v_parserState_2417_, lean_object* v_cmdState_2418_, lean_object* v_prom_2419_, uint8_t v_sync_2420_, lean_object* v_parseCancelTk_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_toSnapshot_2425_; lean_object* v_stx_2426_; lean_object* v_parserState_2427_; lean_object* v_elabSnap_2428_; lean_object* v_val_2429_; lean_object* v_newParserState_2430_; lean_object* v___y_2464_; lean_object* v___y_2466_; lean_object* v___y_2467_; uint8_t v___y_2468_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___y_2511_; lean_object* v___y_2512_; uint8_t v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2536_; uint8_t v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; 
v___f_2506_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2507_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2508_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2509_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2654_; lean_object* v_nextCmdSnap_x3f_2655_; 
v_val_2654_ = lean_ctor_get(v_old_x3f_2416_, 0);
v_nextCmdSnap_x3f_2655_ = lean_ctor_get(v_val_2654_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2655_) == 0)
{
goto v___jp_2621_;
}
else
{
lean_object* v_toSnapshot_2656_; lean_object* v_stx_2657_; lean_object* v_parserState_2658_; lean_object* v_elabSnap_2659_; lean_object* v_val_2660_; lean_object* v___x_2661_; 
v_toSnapshot_2656_ = lean_ctor_get(v_val_2654_, 0);
v_stx_2657_ = lean_ctor_get(v_val_2654_, 1);
v_parserState_2658_ = lean_ctor_get(v_val_2654_, 2);
v_elabSnap_2659_ = lean_ctor_get(v_val_2654_, 3);
v_val_2660_ = lean_ctor_get(v_nextCmdSnap_x3f_2655_, 0);
lean_inc(v_val_2660_);
v___x_2661_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2660_);
if (lean_obj_tag(v___x_2661_) == 1)
{
lean_object* v_val_2662_; lean_object* v_nextCmdSnap_x3f_2663_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref(v___x_2661_);
v_nextCmdSnap_x3f_2663_ = lean_ctor_get(v_val_2662_, 4);
lean_inc(v_nextCmdSnap_x3f_2663_);
lean_dec(v_val_2662_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2663_) == 0)
{
goto v___jp_2621_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2665_; 
v_val_2664_ = lean_ctor_get(v_nextCmdSnap_x3f_2663_, 0);
lean_inc(v_val_2664_);
lean_dec_ref(v_nextCmdSnap_x3f_2663_);
v___x_2665_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2664_);
if (lean_obj_tag(v___x_2665_) == 1)
{
lean_object* v_val_2666_; lean_object* v_parserState_2667_; lean_object* v_pos_2668_; uint8_t v___x_2669_; 
v_val_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_val_2666_);
lean_dec_ref(v___x_2665_);
v_parserState_2667_ = lean_ctor_get(v_val_2666_, 2);
lean_inc_ref(v_parserState_2667_);
lean_dec(v_val_2666_);
v_pos_2668_ = lean_ctor_get(v_parserState_2667_, 0);
lean_inc(v_pos_2668_);
lean_dec_ref(v_parserState_2667_);
v___x_2669_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2668_, v_a_2422_);
lean_dec(v_pos_2668_);
if (v___x_2669_ == 0)
{
goto v___jp_2621_;
}
else
{
lean_inc(v_val_2660_);
lean_inc_ref(v_elabSnap_2659_);
lean_inc_ref_n(v_parserState_2658_, 2);
lean_inc(v_stx_2657_);
lean_inc_ref(v_toSnapshot_2656_);
lean_dec_ref(v_old_x3f_2416_);
lean_dec(v_parseCancelTk_2421_);
lean_dec_ref(v_cmdState_2418_);
lean_dec_ref(v_parserState_2417_);
v_toSnapshot_2425_ = v_toSnapshot_2656_;
v_stx_2426_ = v_stx_2657_;
v_parserState_2427_ = v_parserState_2658_;
v_elabSnap_2428_ = v_elabSnap_2659_;
v_val_2429_ = v_val_2660_;
v_newParserState_2430_ = v_parserState_2658_;
goto v___jp_2424_;
}
}
else
{
lean_dec(v___x_2665_);
goto v___jp_2621_;
}
}
}
else
{
lean_dec(v___x_2661_);
goto v___jp_2621_;
}
}
}
else
{
goto v___jp_2621_;
}
v___jp_2424_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_resultSnap_2433_; lean_object* v_task_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2457_; 
v___x_2431_ = lean_io_promise_new();
v___x_2432_ = l_IO_CancelToken_new();
v_resultSnap_2433_ = lean_ctor_get(v_elabSnap_2428_, 2);
lean_inc_ref(v_resultSnap_2433_);
v_task_2434_ = lean_ctor_get(v_resultSnap_2433_, 3);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_resultSnap_2433_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; lean_object* v_unused_2459_; lean_object* v_unused_2460_; 
v_unused_2458_ = lean_ctor_get(v_resultSnap_2433_, 2);
lean_dec(v_unused_2458_);
v_unused_2459_ = lean_ctor_get(v_resultSnap_2433_, 1);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_resultSnap_2433_, 0);
lean_dec(v_unused_2460_);
v___x_2436_ = v_resultSnap_2433_;
v_isShared_2437_ = v_isSharedCheck_2457_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_task_2434_);
lean_dec(v_resultSnap_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2457_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v_toProcessingContext_2443_; lean_object* v_pos_2444_; lean_object* v_endPos_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2438_ = lean_box(v_sync_2420_);
lean_inc_ref(v_a_2422_);
lean_inc(v___x_2432_);
lean_inc(v___x_2431_);
lean_inc_ref(v_newParserState_2430_);
v___f_2439_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2439_, 0, v_val_2429_);
lean_closure_set(v___f_2439_, 1, v_newParserState_2430_);
lean_closure_set(v___f_2439_, 2, v___x_2431_);
lean_closure_set(v___f_2439_, 3, v___x_2438_);
lean_closure_set(v___f_2439_, 4, v___x_2432_);
lean_closure_set(v___f_2439_, 5, v_a_2422_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = 1;
v___x_2442_ = l_BaseIO_chainTask___redArg(v_task_2434_, v___f_2439_, v___x_2440_, v___x_2441_);
v_toProcessingContext_2443_ = lean_ctor_get(v_a_2422_, 0);
v_pos_2444_ = lean_ctor_get(v_newParserState_2430_, 0);
lean_inc(v_pos_2444_);
lean_dec_ref(v_newParserState_2430_);
v_endPos_2445_ = lean_ctor_get(v_toProcessingContext_2443_, 3);
v___x_2446_ = lean_box(0);
lean_inc(v_endPos_2445_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_pos_2444_);
lean_ctor_set(v___x_2447_, 1, v_endPos_2445_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2432_);
v___x_2450_ = l_IO_Promise_result_x21___redArg(v___x_2431_);
lean_dec(v___x_2431_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 3, v___x_2450_);
lean_ctor_set(v___x_2436_, 2, v___x_2449_);
lean_ctor_set(v___x_2436_, 1, v___x_2448_);
lean_ctor_set(v___x_2436_, 0, v___x_2446_);
v___x_2452_ = v___x_2436_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2454_, 0, v_toSnapshot_2425_);
lean_ctor_set(v___x_2454_, 1, v_stx_2426_);
lean_ctor_set(v___x_2454_, 2, v_parserState_2427_);
lean_ctor_set(v___x_2454_, 3, v_elabSnap_2428_);
lean_ctor_set(v___x_2454_, 4, v___x_2453_);
v___x_2455_ = lean_io_promise_resolve(v___x_2454_, v_prom_2419_);
lean_dec(v_prom_2419_);
return v___x_2455_;
}
}
}
v___jp_2461_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_box(0);
return v___x_2462_;
}
v___jp_2463_:
{
goto v___jp_2461_;
}
v___jp_2465_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2470_ = l_Lean_Name_str___override(v___y_2467_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2472_ = l_Lean_Name_str___override(v___x_2470_, v___x_2471_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2474_ = l_Lean_Name_str___override(v___x_2472_, v___x_2473_);
v___x_2475_ = l_Lean_Name_str___override(v___x_2474_, v___x_2471_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = l_Lean_Name_num___override(v___x_2475_, v___x_2476_);
v___x_2478_ = l_Lean_Name_str___override(v___x_2477_, v___x_2471_);
v___x_2479_ = l_Lean_Name_str___override(v___x_2478_, v___x_2473_);
v___x_2480_ = l_Lean_Name_str___override(v___x_2479_, v___x_2471_);
v___x_2481_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2482_ = l_Lean_Name_str___override(v___x_2480_, v___x_2481_);
v___x_2483_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2484_ = l_Lean_Name_str___override(v___x_2482_, v___x_2483_);
v___x_2485_ = l_Lean_Name_toString(v___x_2484_, v___y_2468_);
v___x_2486_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2489_ = 0;
v___x_2490_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2490_, 0, v___x_2485_);
lean_ctor_set(v___x_2490_, 1, v___x_2486_);
lean_ctor_set(v___x_2490_, 2, v___x_2487_);
lean_ctor_set(v___x_2490_, 3, v___x_2488_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*4, v___x_2489_);
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2490_, 3);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2490_);
lean_ctor_set(v___x_2493_, 1, v_cmdState_2418_);
v___x_2494_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2487_, v___x_2493_);
v___x_2495_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2487_, v___x_2490_);
v___x_2496_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2490_);
lean_ctor_set(v___x_2497_, 1, v___x_2492_);
lean_ctor_set(v___x_2497_, 2, v___x_2494_);
lean_ctor_set(v___x_2497_, 3, v___x_2495_);
lean_ctor_set(v___x_2497_, 4, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2490_);
lean_ctor_set(v___x_2498_, 1, v___x_2491_);
lean_ctor_set(v___x_2498_, 2, v___y_2466_);
lean_ctor_set(v___x_2498_, 3, v___x_2497_);
lean_ctor_set(v___x_2498_, 4, v___x_2487_);
v___x_2499_ = lean_io_promise_resolve(v___x_2498_, v_prom_2419_);
lean_dec(v_prom_2419_);
v___x_2500_ = lean_box(0);
return v___x_2500_;
}
v___jp_2501_:
{
v___y_2466_ = v___y_2502_;
v___y_2467_ = v___y_2503_;
v___y_2468_ = v___y_2504_;
goto v___jp_2465_;
}
v___jp_2510_:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2527_);
v___x_2529_ = l_Lean_Parser_isTerminalCommand(v___y_2521_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_io_promise_new();
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
v___x_2532_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2528_, v___y_2526_, v___y_2520_, v___y_2513_, v_a_2422_, v___y_2522_, v___y_2515_, v___y_2523_, v___y_2517_, v___y_2516_, v___y_2525_, v___y_2524_, v___y_2512_, v_prom_2419_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2514_, v___y_2519_, v_cmdState_2418_, v___y_2518_, v___y_2511_, v_old_x3f_2416_, v_parseCancelTk_2421_, v___x_2531_);
lean_dec_ref(v___y_2518_);
lean_dec(v_prom_2419_);
lean_dec(v___y_2525_);
lean_dec(v___y_2526_);
v___y_2464_ = v___x_2532_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2528_, v___y_2526_, v___y_2520_, v___y_2513_, v_a_2422_, v___y_2522_, v___y_2515_, v___y_2523_, v___y_2517_, v___y_2516_, v___y_2525_, v___y_2524_, v___y_2512_, v_prom_2419_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2514_, v___y_2519_, v_cmdState_2418_, v___y_2518_, v___y_2511_, v_old_x3f_2416_, v_parseCancelTk_2421_, v___x_2533_);
lean_dec_ref(v___y_2518_);
lean_dec(v_prom_2419_);
lean_dec(v___y_2525_);
lean_dec(v___y_2526_);
v___y_2464_ = v___x_2534_;
goto v___jp_2463_;
}
}
v___jp_2535_:
{
lean_object* v___x_2552_; 
lean_inc(v___y_2549_);
v___x_2552_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_box(0);
v___y_2511_ = v___y_2536_;
v___y_2512_ = v_snd_2551_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v_fst_2550_;
v___y_2518_ = v___y_2541_;
v___y_2519_ = v___y_2542_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2549_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___x_2553_;
goto v___jp_2510_;
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2562_; 
v_val_2554_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2556_ = v___x_2552_;
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_val_2554_);
lean_dec(v___x_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_inc(v_val_2554_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_val_2554_);
lean_ctor_set(v___x_2558_, 1, v_val_2554_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2558_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2511_ = v___y_2536_;
v___y_2512_ = v_snd_2551_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v_fst_2550_;
v___y_2518_ = v___y_2541_;
v___y_2519_ = v___y_2542_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2549_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___x_2560_;
goto v___jp_2510_;
}
}
}
}
v___jp_2563_:
{
if (v___y_2579_ == 0)
{
lean_inc(v___y_2577_);
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2567_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2569_;
v___y_2542_ = v___y_2570_;
v___y_2543_ = v___y_2571_;
v___y_2544_ = v___y_2572_;
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v_fst_2550_ = v___y_2577_;
v_snd_2551_ = v___y_2578_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v___y_2578_);
v___x_2580_ = lean_box(0);
v___x_2581_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2567_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2569_;
v___y_2542_ = v___y_2570_;
v___y_2543_ = v___y_2571_;
v___y_2544_ = v___y_2572_;
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v_fst_2550_ = v___x_2580_;
v_snd_2551_ = v___x_2581_;
goto v___jp_2535_;
}
}
v___jp_2582_:
{
uint8_t v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = l_IO_CancelToken_isSet(v_parseCancelTk_2421_);
v___x_2594_ = 1;
if (v___x_2593_ == 0)
{
lean_dec(v___y_2592_);
if (v_sync_2420_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2595_ = lean_io_promise_new();
v___x_2596_ = lean_io_promise_new();
v___x_2597_ = lean_io_promise_new();
v___x_2598_ = lean_io_promise_new();
v___x_2599_ = l_Lean_internal_cmdlineSnapshots;
v___x_2600_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2589_, v___x_2599_);
lean_dec_ref(v___y_2589_);
if (v___x_2600_ == 0)
{
v___y_2564_ = v___x_2599_;
v___y_2565_ = v___x_2593_;
v___y_2566_ = v___y_2586_;
v___y_2567_ = v___y_2587_;
v___y_2568_ = v___x_2595_;
v___y_2569_ = v___y_2584_;
v___y_2570_ = v___y_2583_;
v___y_2571_ = v___y_2585_;
v___y_2572_ = v___y_2588_;
v___y_2573_ = v___x_2594_;
v___y_2574_ = v___x_2597_;
v___y_2575_ = v___x_2596_;
v___y_2576_ = v___x_2598_;
v___y_2577_ = v___y_2590_;
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___x_2600_;
goto v___jp_2563_;
}
else
{
uint8_t v___x_2601_; 
lean_inc(v___y_2590_);
v___x_2601_ = l_Lean_Parser_isTerminalCommand(v___y_2590_);
if (v___x_2601_ == 0)
{
v___y_2564_ = v___x_2599_;
v___y_2565_ = v___x_2593_;
v___y_2566_ = v___y_2586_;
v___y_2567_ = v___y_2587_;
v___y_2568_ = v___x_2595_;
v___y_2569_ = v___y_2584_;
v___y_2570_ = v___y_2583_;
v___y_2571_ = v___y_2585_;
v___y_2572_ = v___y_2588_;
v___y_2573_ = v___x_2594_;
v___y_2574_ = v___x_2597_;
v___y_2575_ = v___x_2596_;
v___y_2576_ = v___x_2598_;
v___y_2577_ = v___y_2590_;
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___x_2600_;
goto v___jp_2563_;
}
else
{
lean_inc(v___y_2590_);
v___y_2536_ = v___x_2599_;
v___y_2537_ = v___x_2593_;
v___y_2538_ = v___y_2586_;
v___y_2539_ = v___y_2587_;
v___y_2540_ = v___x_2595_;
v___y_2541_ = v___y_2584_;
v___y_2542_ = v___y_2583_;
v___y_2543_ = v___y_2585_;
v___y_2544_ = v___y_2588_;
v___y_2545_ = v___x_2594_;
v___y_2546_ = v___x_2597_;
v___y_2547_ = v___x_2596_;
v___y_2548_ = v___x_2598_;
v___y_2549_ = v___y_2590_;
v_fst_2550_ = v___y_2590_;
v_snd_2551_ = v___y_2591_;
goto v___jp_2535_;
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
v___x_2602_ = lean_box(v___x_2593_);
v___x_2603_ = lean_box(v___x_2594_);
lean_inc_ref(v_a_2422_);
v___f_2604_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2604_, 0, v___y_2585_);
lean_closure_set(v___f_2604_, 1, v___x_2602_);
lean_closure_set(v___f_2604_, 2, v_a_2422_);
lean_closure_set(v___f_2604_, 3, v___y_2588_);
lean_closure_set(v___f_2604_, 4, v___y_2587_);
lean_closure_set(v___f_2604_, 5, v___x_2603_);
lean_closure_set(v___f_2604_, 6, v_prom_2419_);
lean_closure_set(v___f_2604_, 7, v___x_2509_);
lean_closure_set(v___f_2604_, 8, v___f_2508_);
lean_closure_set(v___f_2604_, 9, v___f_2507_);
lean_closure_set(v___f_2604_, 10, v___f_2506_);
lean_closure_set(v___f_2604_, 11, v___y_2586_);
lean_closure_set(v___f_2604_, 12, v___y_2583_);
lean_closure_set(v___f_2604_, 13, v_cmdState_2418_);
lean_closure_set(v___f_2604_, 14, v___y_2584_);
lean_closure_set(v___f_2604_, 15, v_old_x3f_2416_);
lean_closure_set(v___f_2604_, 16, v_parseCancelTk_2421_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_io_as_task(v___f_2604_, v___x_2605_);
lean_dec_ref(v___x_2606_);
goto v___jp_2461_;
}
}
else
{
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v_parseCancelTk_2421_);
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2608_; lean_object* v_children_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_val_2607_ = lean_ctor_get(v_old_x3f_2416_, 0);
lean_inc(v_val_2607_);
lean_dec_ref(v_old_x3f_2416_);
v___x_2608_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2607_);
v_children_2609_ = lean_ctor_get(v___x_2608_, 1);
lean_inc_ref(v_children_2609_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_array_get_size(v_children_2609_);
v___x_2612_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_dec_ref(v_children_2609_);
v___y_2466_ = v___y_2591_;
v___y_2467_ = v___y_2592_;
v___y_2468_ = v___x_2594_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_nat_dec_le(v___x_2611_, v___x_2611_);
if (v___x_2614_ == 0)
{
if (v___x_2612_ == 0)
{
lean_dec_ref(v_children_2609_);
v___y_2466_ = v___y_2591_;
v___y_2467_ = v___y_2592_;
v___y_2468_ = v___x_2594_;
goto v___jp_2465_;
}
else
{
size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = lean_usize_of_nat(v___x_2611_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2609_, v___x_2615_, v___x_2616_, v___x_2613_);
lean_dec_ref(v_children_2609_);
v___y_2502_ = v___y_2591_;
v___y_2503_ = v___y_2592_;
v___y_2504_ = v___x_2594_;
v___y_2505_ = v___x_2617_;
goto v___jp_2501_;
}
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2611_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2609_, v___x_2618_, v___x_2619_, v___x_2613_);
lean_dec_ref(v_children_2609_);
v___y_2502_ = v___y_2591_;
v___y_2503_ = v___y_2592_;
v___y_2504_ = v___x_2594_;
v___y_2505_ = v___x_2620_;
goto v___jp_2501_;
}
}
}
else
{
lean_dec(v_old_x3f_2416_);
v___y_2466_ = v___y_2591_;
v___y_2467_ = v___y_2592_;
v___y_2468_ = v___x_2594_;
goto v___jp_2465_;
}
}
}
v___jp_2621_:
{
lean_object* v_env_2622_; lean_object* v_scopes_2623_; lean_object* v___x_2624_; lean_object* v_opts_2625_; lean_object* v_currNamespace_2626_; lean_object* v_openDecls_2627_; lean_object* v___x_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_snd_2633_; 
v_env_2622_ = lean_ctor_get(v_cmdState_2418_, 0);
v_scopes_2623_ = lean_ctor_get(v_cmdState_2418_, 2);
v___x_2624_ = l_List_head_x21___redArg(v___x_2509_, v_scopes_2623_);
v_opts_2625_ = lean_ctor_get(v___x_2624_, 1);
lean_inc_ref_n(v_opts_2625_, 2);
v_currNamespace_2626_ = lean_ctor_get(v___x_2624_, 2);
lean_inc(v_currNamespace_2626_);
v_openDecls_2627_ = lean_ctor_get(v___x_2624_, 3);
lean_inc(v_openDecls_2627_);
lean_dec(v___x_2624_);
lean_inc_ref(v_env_2622_);
v___x_2628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2628_, 0, v_env_2622_);
lean_ctor_set(v___x_2628_, 1, v_opts_2625_);
lean_ctor_set(v___x_2628_, 2, v_currNamespace_2626_);
lean_ctor_set(v___x_2628_, 3, v_openDecls_2627_);
lean_inc_ref(v_parserState_2417_);
lean_inc_ref(v_a_2422_);
v___f_2629_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2629_, 0, v_a_2422_);
lean_closure_set(v___f_2629_, 1, v___x_2628_);
lean_closure_set(v___f_2629_, 2, v_parserState_2417_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_profileit(v___x_2630_, v_opts_2625_, v___f_2629_, v___x_2631_);
v_snd_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_snd_2633_);
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2634_; lean_object* v_fst_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v_pos_2638_; lean_object* v_toSnapshot_2639_; lean_object* v_stx_2640_; lean_object* v_parserState_2641_; lean_object* v_elabSnap_2642_; lean_object* v_nextCmdSnap_x3f_2643_; uint8_t v___x_2644_; 
v_val_2634_ = lean_ctor_get(v_old_x3f_2416_, 0);
v_fst_2635_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_n(v_fst_2635_, 2);
lean_dec(v___x_2632_);
v_fst_2636_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v_snd_2633_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_snd_2633_);
v_pos_2638_ = lean_ctor_get(v_parserState_2417_, 0);
lean_inc(v_pos_2638_);
lean_dec_ref(v_parserState_2417_);
v_toSnapshot_2639_ = lean_ctor_get(v_val_2634_, 0);
v_stx_2640_ = lean_ctor_get(v_val_2634_, 1);
v_parserState_2641_ = lean_ctor_get(v_val_2634_, 2);
v_elabSnap_2642_ = lean_ctor_get(v_val_2634_, 3);
v_nextCmdSnap_x3f_2643_ = lean_ctor_get(v_val_2634_, 4);
lean_inc(v_stx_2640_);
v___x_2644_ = l_Lean_Syntax_eqWithInfo(v_fst_2635_, v_stx_2640_);
if (v___x_2644_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2643_) == 0)
{
lean_inc(v_fst_2636_);
lean_inc_ref(v_opts_2625_);
lean_inc(v_fst_2635_);
v___y_2583_ = v_fst_2635_;
v___y_2584_ = v_opts_2625_;
v___y_2585_ = v_fst_2636_;
v___y_2586_ = v_pos_2638_;
v___y_2587_ = v___x_2631_;
v___y_2588_ = v_snd_2637_;
v___y_2589_ = v_opts_2625_;
v___y_2590_ = v_fst_2635_;
v___y_2591_ = v_fst_2636_;
v___y_2592_ = v___x_2631_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_val_2645_ = lean_ctor_get(v_nextCmdSnap_x3f_2643_, 0);
v___x_2646_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2645_);
v___x_2647_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2646_, v_val_2645_);
lean_inc(v_fst_2636_);
lean_inc_ref(v_opts_2625_);
lean_inc(v_fst_2635_);
v___y_2583_ = v_fst_2635_;
v___y_2584_ = v_opts_2625_;
v___y_2585_ = v_fst_2636_;
v___y_2586_ = v_pos_2638_;
v___y_2587_ = v___x_2631_;
v___y_2588_ = v_snd_2637_;
v___y_2589_ = v_opts_2625_;
v___y_2590_ = v_fst_2635_;
v___y_2591_ = v_fst_2636_;
v___y_2592_ = v___x_2631_;
goto v___jp_2582_;
}
}
else
{
lean_inc(v_val_2634_);
lean_dec(v_pos_2638_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2635_);
lean_dec_ref(v_old_x3f_2416_);
lean_dec_ref(v_opts_2625_);
lean_dec(v_parseCancelTk_2421_);
lean_dec_ref(v_cmdState_2418_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2643_) == 1)
{
lean_object* v_val_2648_; 
lean_inc_ref(v_nextCmdSnap_x3f_2643_);
lean_inc_ref(v_elabSnap_2642_);
lean_inc_ref(v_parserState_2641_);
lean_inc(v_stx_2640_);
lean_inc_ref(v_toSnapshot_2639_);
lean_dec(v_val_2634_);
v_val_2648_ = lean_ctor_get(v_nextCmdSnap_x3f_2643_, 0);
lean_inc(v_val_2648_);
lean_dec_ref(v_nextCmdSnap_x3f_2643_);
v_toSnapshot_2425_ = v_toSnapshot_2639_;
v_stx_2426_ = v_stx_2640_;
v_parserState_2427_ = v_parserState_2641_;
v_elabSnap_2428_ = v_elabSnap_2642_;
v_val_2429_ = v_val_2648_;
v_newParserState_2430_ = v_fst_2636_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2649_; 
lean_dec(v_fst_2636_);
v___x_2649_ = lean_io_promise_resolve(v_val_2634_, v_prom_2419_);
lean_dec(v_prom_2419_);
return v___x_2649_;
}
}
}
else
{
lean_object* v_fst_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v_pos_2653_; 
v_fst_2650_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_n(v_fst_2650_, 2);
lean_dec(v___x_2632_);
v_fst_2651_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc_n(v_fst_2651_, 2);
v_snd_2652_ = lean_ctor_get(v_snd_2633_, 1);
lean_inc(v_snd_2652_);
lean_dec(v_snd_2633_);
v_pos_2653_ = lean_ctor_get(v_parserState_2417_, 0);
lean_inc(v_pos_2653_);
lean_dec_ref(v_parserState_2417_);
lean_inc_ref(v_opts_2625_);
v___y_2583_ = v_fst_2650_;
v___y_2584_ = v_opts_2625_;
v___y_2585_ = v_fst_2651_;
v___y_2586_ = v_pos_2653_;
v___y_2587_ = v___x_2631_;
v___y_2588_ = v_snd_2652_;
v___y_2589_ = v_opts_2625_;
v___y_2590_ = v_fst_2650_;
v___y_2591_ = v_fst_2651_;
v___y_2592_ = v___x_2631_;
goto v___jp_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2670_, lean_object* v_newParserState_2671_, lean_object* v_val_2672_, uint8_t v_sync_2673_, lean_object* v_val_2674_, lean_object* v_a_2675_, lean_object* v_oldNext_2676_){
_start:
{
lean_object* v_cmdState_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_cmdState_2678_ = lean_ctor_get(v_oldResult_2670_, 1);
lean_inc_ref(v_cmdState_2678_);
lean_dec_ref(v_oldResult_2670_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_oldNext_2676_);
v___x_2680_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2679_, v_newParserState_2671_, v_cmdState_2678_, v_val_2672_, v_sync_2673_, v_val_2674_, v_a_2675_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2681_ = _args[0];
lean_object* v_val_2682_ = _args[1];
lean_object* v_fst_2683_ = _args[2];
lean_object* v_val_2684_ = _args[3];
lean_object* v_a_2685_ = _args[4];
lean_object* v_snd_2686_ = _args[5];
lean_object* v___x_2687_ = _args[6];
lean_object* v___x_2688_ = _args[7];
lean_object* v_fst_2689_ = _args[8];
lean_object* v_val_2690_ = _args[9];
lean_object* v_val_2691_ = _args[10];
lean_object* v_val_2692_ = _args[11];
lean_object* v_snd_2693_ = _args[12];
lean_object* v_prom_2694_ = _args[13];
lean_object* v___x_2695_ = _args[14];
lean_object* v___f_2696_ = _args[15];
lean_object* v___f_2697_ = _args[16];
lean_object* v___f_2698_ = _args[17];
lean_object* v_pos_2699_ = _args[18];
lean_object* v_fst_2700_ = _args[19];
lean_object* v_cmdState_2701_ = _args[20];
lean_object* v_opts_2702_ = _args[21];
lean_object* v___x_2703_ = _args[22];
lean_object* v_old_x3f_2704_ = _args[23];
lean_object* v_parseCancelTk_2705_ = _args[24];
lean_object* v_next_x3f_2706_ = _args[25];
lean_object* v___y_2707_ = _args[26];
_start:
{
uint8_t v_val_45499__boxed_2708_; uint8_t v___x_45502__boxed_2709_; lean_object* v_res_2710_; 
v_val_45499__boxed_2708_ = lean_unbox(v_val_2684_);
v___x_45502__boxed_2709_ = lean_unbox(v___x_2688_);
v_res_2710_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2681_, v_val_2682_, v_fst_2683_, v_val_45499__boxed_2708_, v_a_2685_, v_snd_2686_, v___x_2687_, v___x_45502__boxed_2709_, v_fst_2689_, v_val_2690_, v_val_2691_, v_val_2692_, v_snd_2693_, v_prom_2694_, v___x_2695_, v___f_2696_, v___f_2697_, v___f_2698_, v_pos_2699_, v_fst_2700_, v_cmdState_2701_, v_opts_2702_, v___x_2703_, v_old_x3f_2704_, v_parseCancelTk_2705_, v_next_x3f_2706_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v_opts_2702_);
lean_dec(v_prom_2694_);
lean_dec(v_val_2691_);
lean_dec_ref(v_a_2685_);
lean_dec(v_val_2682_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2711_, lean_object* v_parserState_2712_, lean_object* v_cmdState_2713_, lean_object* v_prom_2714_, lean_object* v_sync_2715_, lean_object* v_parseCancelTk_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_sync_boxed_2719_; lean_object* v_res_2720_; 
v_sync_boxed_2719_ = lean_unbox(v_sync_2715_);
v_res_2720_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2711_, v_parserState_2712_, v_cmdState_2713_, v_prom_2714_, v_sync_boxed_2719_, v_parseCancelTk_2716_, v_a_2717_);
lean_dec_ref(v_a_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2721_, size_t v_i_2722_, size_t v_stop_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2721_, v_i_2722_, v_stop_2723_, v_b_2724_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2728_, lean_object* v_i_2729_, lean_object* v_stop_2730_, lean_object* v_b_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
size_t v_i_boxed_2734_; size_t v_stop_boxed_2735_; lean_object* v_res_2736_; 
v_i_boxed_2734_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_stop_boxed_2735_ = lean_unbox_usize(v_stop_2730_);
lean_dec(v_stop_2730_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2728_, v_i_boxed_2734_, v_stop_boxed_2735_, v_b_2731_, v___y_2732_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_as_2728_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2737_, lean_object* v_opt_2738_){
_start:
{
lean_object* v_name_2739_; lean_object* v_map_2740_; lean_object* v___x_2741_; 
v_name_2739_ = lean_ctor_get(v_opt_2738_, 0);
v_map_2740_ = lean_ctor_get(v_opts_2737_, 0);
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2740_, v_name_2739_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_box(0);
return v___x_2742_;
}
else
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2752_; 
v_val_2743_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
if (lean_obj_tag(v_val_2743_) == 0)
{
lean_object* v_v_2747_; lean_object* v___x_2749_; 
v_v_2747_ = lean_ctor_get(v_val_2743_, 0);
lean_inc_ref(v_v_2747_);
lean_dec_ref(v_val_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_v_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_v_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
else
{
lean_object* v___x_2751_; 
lean_del_object(v___x_2745_);
lean_dec(v_val_2743_);
v___x_2751_ = lean_box(0);
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2753_, lean_object* v_opt_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2753_, v_opt_2754_);
lean_dec_ref(v_opt_2754_);
lean_dec_ref(v_opts_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2756_);
v___x_2759_ = lean_box(0);
v___x_2760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2760_, 0, v_x_2757_);
lean_ctor_set(v___x_2760_, 1, v___x_2758_);
lean_ctor_set(v___x_2760_, 2, v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2767_ = l_Array_toPArray_x27___redArg(v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
if (lean_obj_tag(v_a_2768_) == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = l_List_reverse___redArg(v_a_2769_);
return v___x_2770_;
}
else
{
lean_object* v_head_2771_; lean_object* v_tail_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2785_; 
v_head_2771_ = lean_ctor_get(v_a_2768_, 0);
v_tail_2772_ = lean_ctor_get(v_a_2768_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_a_2768_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2774_ = v_a_2768_;
v_isShared_2775_ = v_isSharedCheck_2785_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_tail_2772_);
lean_inc(v_head_2771_);
lean_dec(v_a_2768_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2785_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2776_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_head_2771_);
v___x_2778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
v___x_2779_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 1, v_a_2769_);
lean_ctor_set(v___x_2774_, 0, v___x_2780_);
v___x_2782_ = v___x_2774_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_a_2769_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
v_a_2768_ = v_tail_2772_;
v_a_2769_ = v___x_2782_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2796_; double v___x_2797_; 
v___x_2796_ = lean_unsigned_to_nat(1000000000u);
v___x_2797_ = lean_float_of_nat(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2805_ = l_Lean_MessageData_ofFormat(v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2806_, lean_object* v_stx_2807_, lean_object* v_toProcessingContext_2808_, lean_object* v___x_2809_, lean_object* v_fileMap_2810_, lean_object* v_parserState_2811_, lean_object* v_a_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_toProcessingContext_2817_; lean_object* v___x_2818_; 
v_toProcessingContext_2817_ = lean_ctor_get(v___y_2815_, 0);
lean_inc_ref(v_toProcessingContext_2817_);
lean_inc(v_stx_2807_);
v___x_2818_ = lean_apply_3(v_setupImports_2806_, v_stx_2807_, v_toProcessingContext_2817_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_3027_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_3027_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_3027_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
if (lean_obj_tag(v_a_2819_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; 
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v_parserState_2811_);
lean_dec_ref(v_fileMap_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v_toProcessingContext_2808_);
lean_dec(v_stx_2807_);
v_a_2823_ = lean_ctor_get(v_a_2819_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v_a_2819_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_a_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_3026_; 
v_a_2827_ = lean_ctor_get(v_a_2819_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2829_ = v_a_2819_;
v_isShared_2830_ = v_isSharedCheck_3026_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v_a_2819_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_3026_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v_mainModuleName_2832_; lean_object* v_package_x3f_2833_; uint8_t v_isModule_2834_; lean_object* v_imports_2835_; lean_object* v_opts_2836_; uint32_t v_trustLevel_2837_; lean_object* v_importArts_2838_; lean_object* v_plugins_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2831_ = lean_io_mono_nanos_now();
v_mainModuleName_2832_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_mainModuleName_2832_);
v_package_x3f_2833_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_package_x3f_2833_);
v_isModule_2834_ = lean_ctor_get_uint8(v_a_2827_, sizeof(void*)*6 + 4);
v_imports_2835_ = lean_ctor_get(v_a_2827_, 2);
lean_inc_ref(v_imports_2835_);
v_opts_2836_ = lean_ctor_get(v_a_2827_, 3);
lean_inc_ref_n(v_opts_2836_, 2);
v_trustLevel_2837_ = lean_ctor_get_uint32(v_a_2827_, sizeof(void*)*6);
v_importArts_2838_ = lean_ctor_get(v_a_2827_, 4);
lean_inc(v_importArts_2838_);
v_plugins_2839_ = lean_ctor_get(v_a_2827_, 5);
lean_inc_ref(v_plugins_2839_);
lean_dec(v_a_2827_);
v___x_2840_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2807_);
v___x_2841_ = l_Lean_MessageLog_empty;
v___x_2842_ = 1;
v___x_2843_ = l_Lean_Elab_processHeaderCore(v___x_2840_, v_imports_2835_, v_isModule_2834_, v_opts_2836_, v___x_2841_, v_toProcessingContext_2808_, v_trustLevel_2837_, v_plugins_2839_, v___x_2842_, v_mainModuleName_2832_, v_package_x3f_2833_, v_importArts_2838_);
lean_dec(v___x_2840_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_3017_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_3017_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_3017_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_3016_; 
v_fst_2848_ = lean_ctor_get(v_a_2844_, 0);
v_snd_2849_ = lean_ctor_get(v_a_2844_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_a_2844_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2851_ = v_a_2844_;
v_isShared_2852_ = v_isSharedCheck_3016_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snd_2849_);
lean_inc(v_fst_2848_);
lean_dec(v_a_2844_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_3016_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v_traceState_2873_; 
v___x_2853_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2849_);
v___x_2854_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2849_);
v___x_2855_ = l_Lean_MessageLog_hasErrors(v_snd_2849_);
if (v___x_2855_ == 0)
{
double v___x_2966_; double v___x_2967_; double v___x_2968_; double v___x_2969_; double v___x_2970_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_del_object(v___x_2821_);
lean_dec_ref(v___x_2814_);
v___x_2966_ = lean_float_of_nat(v___x_2831_);
v___x_2967_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2968_ = lean_float_div(v___x_2966_, v___x_2967_);
v___x_2969_ = lean_float_of_nat(v___x_2853_);
v___x_2970_ = lean_float_div(v___x_2969_, v___x_2967_);
v___x_2987_ = l_Lean_trace_profiler_output;
v___x_2988_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2836_, v___x_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
if (v___x_2855_ == 0)
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2873_ = v___x_2989_;
goto v___jp_2872_;
}
else
{
goto v___jp_2971_;
}
}
else
{
lean_dec_ref(v___x_2988_);
goto v___jp_2971_;
}
v___jp_2971_:
{
uint64_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2972_ = 0ULL;
v___x_2973_ = lean_box(0);
v___x_2974_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2975_ = lean_box(0);
v___x_2976_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2977_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2977_, 0, v___x_2974_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
lean_ctor_set(v___x_2977_, 2, v___x_2976_);
lean_ctor_set_float(v___x_2977_, sizeof(void*)*3, v___x_2968_);
lean_ctor_set_float(v___x_2977_, sizeof(void*)*3 + 8, v___x_2970_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*3 + 16, v___x_2842_);
v___x_2978_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2979_ = lean_mk_empty_array_with_capacity(v___x_2809_);
v___x_2980_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2977_);
lean_ctor_set(v___x_2980_, 1, v___x_2978_);
lean_ctor_set(v___x_2980_, 2, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2973_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = lean_unsigned_to_nat(1u);
v___x_2983_ = lean_mk_empty_array_with_capacity(v___x_2982_);
v___x_2984_ = lean_array_push(v___x_2983_, v___x_2981_);
v___x_2985_ = l_Array_toPArray_x27___redArg(v___x_2984_);
lean_dec_ref(v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set_uint64(v___x_2986_, sizeof(void*)*1, v___x_2972_);
v_traceState_2873_ = v___x_2986_;
goto v___jp_2872_;
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint64_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; size_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
lean_dec(v___x_2853_);
lean_del_object(v___x_2851_);
lean_dec(v_snd_2849_);
lean_dec(v_fst_2848_);
lean_del_object(v___x_2846_);
lean_dec_ref(v_opts_2836_);
lean_dec(v___x_2831_);
lean_del_object(v___x_2829_);
lean_dec(v___x_2813_);
lean_dec_ref(v_parserState_2811_);
lean_dec_ref(v_fileMap_2810_);
lean_dec(v_stx_2807_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2991_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2992_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2809_, 2);
v___x_2993_ = l_Lean_Name_num___override(v___x_2992_, v___x_2809_);
v___x_2994_ = l_Lean_Name_str___override(v___x_2993_, v___x_2990_);
v___x_2995_ = l_Lean_Name_str___override(v___x_2994_, v___x_2991_);
v___x_2996_ = l_Lean_Name_str___override(v___x_2995_, v___x_2990_);
v___x_2997_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2998_ = l_Lean_Name_str___override(v___x_2996_, v___x_2997_);
v___x_2999_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3000_ = l_Lean_Name_str___override(v___x_2998_, v___x_2999_);
v___x_3001_ = l_Lean_Name_toString(v___x_3000_, v___x_2842_);
v___x_3002_ = lean_box(0);
v___x_3003_ = 0ULL;
v___x_3004_ = lean_unsigned_to_nat(32u);
v___x_3005_ = lean_mk_empty_array_with_capacity(v___x_3004_);
v___x_3006_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3007_ = ((size_t)5ULL);
v___x_3008_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3005_);
lean_ctor_set(v___x_3008_, 2, v___x_2809_);
lean_ctor_set(v___x_3008_, 3, v___x_2809_);
lean_ctor_set_usize(v___x_3008_, 4, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set_uint64(v___x_3009_, sizeof(void*)*1, v___x_3003_);
v___x_3010_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3010_, 0, v___x_3001_);
lean_ctor_set(v___x_3010_, 1, v___x_2854_);
lean_ctor_set(v___x_3010_, 2, v___x_3002_);
lean_ctor_set(v___x_3010_, 3, v___x_3009_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*4, v___x_2855_);
v___x_3011_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2814_);
v___x_3012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
lean_ctor_set(v___x_3012_, 2, v___x_3002_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_3012_);
v___x_3014_ = v___x_2821_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
v___jp_2856_:
{
lean_object* v___x_2864_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___y_2862_);
v___x_2864_ = v___x_2829_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___y_2862_);
v___x_2864_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2865_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2865_, 0, v___y_2859_);
lean_ctor_set(v___x_2865_, 1, v___x_2854_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
lean_ctor_set(v___x_2865_, 3, v___y_2858_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*4, v___x_2855_);
v___x_2866_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2861_, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2867_, 0, v___y_2857_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
lean_ctor_set(v___x_2867_, 2, v___y_2860_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2867_);
v___x_2869_ = v___x_2846_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
v___jp_2872_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Language_Lean_reparseOptions(v_opts_2836_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_env_2881_; lean_object* v_messages_2882_; lean_object* v_scopes_2883_; lean_object* v_usedQuotCtxts_2884_; lean_object* v_nextMacroScope_2885_; lean_object* v_maxRecDepth_2886_; lean_object* v_ngen_2887_; lean_object* v_auxDeclNGen_2888_; lean_object* v_snapshotTasks_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2955_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2809_, 3);
v___x_2877_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2809_);
lean_ctor_set(v___x_2877_, 1, v___x_2809_);
lean_ctor_set(v___x_2877_, 2, v___x_2809_);
lean_ctor_set(v___x_2877_, 3, v___x_2876_);
lean_ctor_set(v___x_2877_, 4, v___x_2876_);
lean_ctor_set(v___x_2877_, 5, v___x_2876_);
lean_ctor_set(v___x_2877_, 6, v___x_2876_);
lean_ctor_set(v___x_2877_, 7, v___x_2876_);
lean_ctor_set(v___x_2877_, 8, v___x_2876_);
v___x_2878_ = lean_io_promise_new();
v___x_2879_ = l_IO_CancelToken_new();
lean_inc(v_fst_2848_);
v___x_2880_ = l_Lean_Elab_Command_mkState(v_fst_2848_, v_snd_2849_, v_a_2875_);
v_env_2881_ = lean_ctor_get(v___x_2880_, 0);
v_messages_2882_ = lean_ctor_get(v___x_2880_, 1);
v_scopes_2883_ = lean_ctor_get(v___x_2880_, 2);
v_usedQuotCtxts_2884_ = lean_ctor_get(v___x_2880_, 3);
v_nextMacroScope_2885_ = lean_ctor_get(v___x_2880_, 4);
v_maxRecDepth_2886_ = lean_ctor_get(v___x_2880_, 5);
v_ngen_2887_ = lean_ctor_get(v___x_2880_, 6);
v_auxDeclNGen_2888_ = lean_ctor_get(v___x_2880_, 7);
v_snapshotTasks_2889_ = lean_ctor_get(v___x_2880_, 10);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; lean_object* v_unused_2957_; 
v_unused_2956_ = lean_ctor_get(v___x_2880_, 9);
lean_dec(v_unused_2956_);
v_unused_2957_ = lean_ctor_get(v___x_2880_, 8);
lean_dec(v_unused_2957_);
v___x_2891_ = v___x_2880_;
v_isShared_2892_ = v_isSharedCheck_2955_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snapshotTasks_2889_);
lean_inc(v_auxDeclNGen_2888_);
lean_inc(v_ngen_2887_);
lean_inc(v_maxRecDepth_2886_);
lean_inc(v_nextMacroScope_2885_);
lean_inc(v_usedQuotCtxts_2884_);
lean_inc(v_scopes_2883_);
lean_inc(v_messages_2882_);
lean_inc(v_env_2881_);
lean_dec(v___x_2880_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2955_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = l_Lean_Options_empty;
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_unsigned_to_nat(1u);
v___x_2898_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2899_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2899_, 0, v_fst_2848_);
lean_ctor_set(v___x_2899_, 1, v___x_2893_);
lean_ctor_set(v___x_2899_, 2, v_fileMap_2810_);
lean_ctor_set(v___x_2899_, 3, v___x_2877_);
lean_ctor_set(v___x_2899_, 4, v___x_2894_);
lean_ctor_set(v___x_2899_, 5, v___x_2895_);
lean_ctor_set(v___x_2899_, 6, v___x_2896_);
lean_ctor_set(v___x_2899_, 7, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2807_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_stx_2807_);
lean_ctor_set(v___x_2851_, 0, v___x_2901_);
v___x_2903_ = v___x_2851_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_stx_2807_);
v___x_2903_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = lean_unsigned_to_nat(2u);
v___x_2906_ = l_Lean_Syntax_getArg(v_stx_2807_, v___x_2905_);
v___x_2907_ = l_Lean_Syntax_getArgs(v___x_2906_);
lean_dec(v___x_2906_);
v___x_2908_ = lean_array_to_list(v___x_2907_);
v___x_2909_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2908_, v___x_2896_);
v___x_2910_ = l_List_toPArray_x27___redArg(v___x_2909_);
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2904_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2900_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_2914_ = lean_array_push(v___x_2913_, v___x_2912_);
v___x_2915_ = l_Array_toPArray_x27___redArg(v___x_2914_);
lean_dec_ref(v___x_2914_);
lean_inc_ref(v___x_2915_);
v___x_2916_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2916_, 0, v___x_2876_);
lean_ctor_set(v___x_2916_, 1, v___x_2876_);
lean_ctor_set(v___x_2916_, 2, v___x_2915_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*3, v___x_2842_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 9, v_traceState_2873_);
lean_ctor_set(v___x_2891_, 8, v___x_2916_);
v___x_2918_ = v___x_2891_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_env_2881_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_messages_2882_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_scopes_2883_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_usedQuotCtxts_2884_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_nextMacroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2953_, 5, v_maxRecDepth_2886_);
lean_ctor_set(v_reuseFailAlloc_2953_, 6, v_ngen_2887_);
lean_ctor_set(v_reuseFailAlloc_2953_, 7, v_auxDeclNGen_2888_);
lean_ctor_set(v_reuseFailAlloc_2953_, 8, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2953_, 9, v_traceState_2873_);
lean_ctor_set(v_reuseFailAlloc_2953_, 10, v_snapshotTasks_2889_);
v___x_2918_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; size_t v___x_2927_; lean_object* v___x_2928_; lean_object* v_size_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint64_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
lean_inc(v___x_2879_);
lean_inc(v___x_2878_);
lean_inc_ref(v___x_2918_);
v___x_2919_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2893_, v_parserState_2811_, v___x_2918_, v___x_2878_, v___x_2842_, v___x_2879_, v_a_2812_);
v___x_2920_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2921_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2922_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2809_, 3);
v___x_2923_ = l_Lean_Name_num___override(v___x_2922_, v___x_2809_);
v___x_2924_ = lean_unsigned_to_nat(32u);
v___x_2925_ = lean_mk_empty_array_with_capacity(v___x_2924_);
v___x_2926_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2927_ = ((size_t)5ULL);
v___x_2928_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2925_);
lean_ctor_set(v___x_2928_, 2, v___x_2809_);
lean_ctor_set(v___x_2928_, 3, v___x_2809_);
lean_ctor_set_usize(v___x_2928_, 4, v___x_2927_);
v_size_2929_ = lean_ctor_get(v___x_2915_, 2);
lean_inc(v_size_2929_);
v___x_2930_ = l_Lean_Name_str___override(v___x_2923_, v___x_2920_);
v___x_2931_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2813_);
v___x_2932_ = l_Lean_Name_str___override(v___x_2930_, v___x_2921_);
v___x_2933_ = l_Lean_Name_str___override(v___x_2932_, v___x_2920_);
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2935_ = l_Lean_Name_str___override(v___x_2933_, v___x_2934_);
v___x_2936_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2937_ = l_Lean_Name_str___override(v___x_2935_, v___x_2936_);
v___x_2938_ = l_Lean_Name_toString(v___x_2937_, v___x_2842_);
v___x_2939_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2940_ = 0ULL;
v___x_2941_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2941_, 0, v___x_2928_);
lean_ctor_set_uint64(v___x_2941_, sizeof(void*)*1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2879_);
v___x_2943_ = l_IO_Promise_result_x21___redArg(v___x_2878_);
lean_dec(v___x_2878_);
v___x_2944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2813_);
lean_ctor_set(v___x_2944_, 1, v___x_2931_);
lean_ctor_set(v___x_2944_, 2, v___x_2942_);
lean_ctor_set(v___x_2944_, 3, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2918_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_inc_ref(v___x_2941_);
lean_inc_ref(v___x_2938_);
v___x_2947_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2947_, 0, v___x_2938_);
lean_ctor_set(v___x_2947_, 1, v___x_2939_);
lean_ctor_set(v___x_2947_, 2, v___x_2893_);
lean_ctor_set(v___x_2947_, 3, v___x_2941_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*4, v___x_2855_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_stx_2807_);
v___x_2949_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2950_ = lean_nat_dec_lt(v___x_2809_, v_size_2929_);
lean_dec(v_size_2929_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec_ref(v___x_2915_);
lean_dec(v___x_2809_);
v___x_2951_ = l_outOfBounds___redArg(v___x_2949_);
v___y_2857_ = v___x_2947_;
v___y_2858_ = v___x_2941_;
v___y_2859_ = v___x_2938_;
v___y_2860_ = v___x_2946_;
v___y_2861_ = v___x_2948_;
v___y_2862_ = v___x_2951_;
goto v___jp_2856_;
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2949_, v___x_2915_, v___x_2809_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2915_);
v___y_2857_ = v___x_2947_;
v___y_2858_ = v___x_2941_;
v___y_2859_ = v___x_2938_;
v___y_2860_ = v___x_2946_;
v___y_2861_ = v___x_2948_;
v___y_2862_ = v___x_2952_;
goto v___jp_2856_;
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v_traceState_2873_);
lean_dec_ref(v___x_2854_);
lean_del_object(v___x_2851_);
lean_dec(v_snd_2849_);
lean_dec(v_fst_2848_);
lean_del_object(v___x_2846_);
lean_del_object(v___x_2829_);
lean_dec(v___x_2813_);
lean_dec_ref(v_parserState_2811_);
lean_dec_ref(v_fileMap_2810_);
lean_dec(v___x_2809_);
lean_dec(v_stx_2807_);
v_a_2958_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2874_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2874_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v_opts_2836_);
lean_dec(v___x_2831_);
lean_del_object(v___x_2829_);
lean_del_object(v___x_2821_);
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v_parserState_2811_);
lean_dec_ref(v_fileMap_2810_);
lean_dec(v___x_2809_);
lean_dec(v_stx_2807_);
v_a_3018_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2843_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2843_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v_parserState_2811_);
lean_dec_ref(v_fileMap_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v_toProcessingContext_2808_);
lean_dec(v_stx_2807_);
v_a_3028_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2818_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2818_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3036_, lean_object* v_stx_3037_, lean_object* v_toProcessingContext_3038_, lean_object* v___x_3039_, lean_object* v_fileMap_3040_, lean_object* v_parserState_3041_, lean_object* v_a_3042_, lean_object* v___x_3043_, lean_object* v___x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3036_, v_stx_3037_, v_toProcessingContext_3038_, v___x_3039_, v_fileMap_3040_, v_parserState_3041_, v_a_3042_, v___x_3043_, v___x_3044_, v___y_3045_);
lean_dec_ref(v___y_3045_);
lean_dec_ref(v_a_3042_);
return v_res_3047_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___f_3049_; 
v___x_3048_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3049_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3049_, 0, v___x_3048_);
return v___f_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3050_, lean_object* v_stx_3051_, lean_object* v_parserState_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_toProcessingContext_3055_; lean_object* v_fileMap_3056_; lean_object* v_endPos_3057_; lean_object* v___x_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_toProcessingContext_3055_ = lean_ctor_get(v_a_3053_, 0);
v_fileMap_3056_ = lean_ctor_get(v_toProcessingContext_3055_, 2);
v_endPos_3057_ = lean_ctor_get(v_toProcessingContext_3055_, 3);
v___x_3058_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3059_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3060_ = lean_box(0);
v___x_3061_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3053_, 2);
lean_inc_ref(v_fileMap_3056_);
lean_inc_ref(v_toProcessingContext_3055_);
v___f_3062_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 11, 9);
lean_closure_set(v___f_3062_, 0, v_setupImports_3050_);
lean_closure_set(v___f_3062_, 1, v_stx_3051_);
lean_closure_set(v___f_3062_, 2, v_toProcessingContext_3055_);
lean_closure_set(v___f_3062_, 3, v___x_3061_);
lean_closure_set(v___f_3062_, 4, v_fileMap_3056_);
lean_closure_set(v___f_3062_, 5, v_parserState_3052_);
lean_closure_set(v___f_3062_, 6, v_a_3053_);
lean_closure_set(v___f_3062_, 7, v___x_3060_);
lean_closure_set(v___f_3062_, 8, v___x_3058_);
lean_inc(v_endPos_3057_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v_endPos_3057_);
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
v___x_3065_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3065_, 0, lean_box(0));
lean_closure_set(v___x_3065_, 1, v___f_3059_);
lean_closure_set(v___x_3065_, 2, v___f_3062_);
lean_closure_set(v___x_3065_, 3, v_a_3053_);
v___x_3066_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3060_, v___x_3060_, v___x_3064_, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3067_, lean_object* v_stx_3068_, lean_object* v_parserState_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3067_, v_stx_3068_, v_parserState_3069_, v_a_3070_);
lean_dec_ref(v_a_3070_);
return v_res_3072_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_box(0);
v___x_3074_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3073_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = 1;
v___x_3080_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3081_ = l_Lean_Name_toString(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3082_ = 0;
v___x_3083_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3084_ = lean_box(0);
v___x_3085_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3086_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3087_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set(v___x_3087_, 1, v___x_3085_);
lean_ctor_set(v___x_3087_, 2, v___x_3084_);
lean_ctor_set(v___x_3087_, 3, v___x_3083_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*4, v___x_3082_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3088_, lean_object* v_cmdState_3089_, lean_object* v_a_3090_, lean_object* v_toSnapshot_3091_, lean_object* v_newStx_3092_, lean_object* v_oldCmd_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v_diagnostics_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3122_; 
v___x_3095_ = lean_io_promise_new();
v___x_3096_ = l_IO_CancelToken_new();
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_oldCmd_3093_);
v___x_3098_ = 1;
lean_inc(v___x_3096_);
lean_inc(v___x_3095_);
lean_inc_ref(v_cmdState_3089_);
v___x_3099_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3097_, v_newParserState_3088_, v_cmdState_3089_, v___x_3095_, v___x_3098_, v___x_3096_, v_a_3090_);
v_diagnostics_3100_ = lean_ctor_get(v_toSnapshot_3091_, 1);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_toSnapshot_3091_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; 
v_unused_3123_ = lean_ctor_get(v_toSnapshot_3091_, 3);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_toSnapshot_3091_, 2);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_toSnapshot_3091_, 0);
lean_dec(v_unused_3125_);
v___x_3102_ = v_toSnapshot_3091_;
v_isShared_3103_ = v_isSharedCheck_3122_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_diagnostics_3100_);
lean_dec(v_toSnapshot_3091_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3122_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3106_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3107_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3096_);
v___x_3109_ = l_IO_Promise_result_x21___redArg(v___x_3095_);
lean_dec(v___x_3095_);
v___x_3110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3104_);
lean_ctor_set(v___x_3110_, 1, v___x_3105_);
lean_ctor_set(v___x_3110_, 2, v___x_3108_);
lean_ctor_set(v___x_3110_, 3, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_cmdState_3089_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
v___x_3113_ = 0;
v___x_3114_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v_newStx_3092_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 3, v___x_3107_);
lean_ctor_set(v___x_3102_, 2, v___x_3104_);
lean_ctor_set(v___x_3102_, 0, v___x_3106_);
v___x_3117_ = v___x_3102_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_diagnostics_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v___x_3107_);
v___x_3117_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*4, v___x_3113_);
v___x_3118_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3115_, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3114_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
lean_ctor_set(v___x_3119_, 2, v___x_3112_);
v___x_3120_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3104_, v___x_3119_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3126_, lean_object* v_cmdState_3127_, lean_object* v_a_3128_, lean_object* v_toSnapshot_3129_, lean_object* v_newStx_3130_, lean_object* v_oldCmd_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3126_, v_cmdState_3127_, v_a_3128_, v_toSnapshot_3129_, v_newStx_3130_, v_oldCmd_3131_);
lean_dec_ref(v_a_3128_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3134_, lean_object* v_a_3135_, lean_object* v_newStx_3136_, lean_object* v___x_3137_, lean_object* v_oldProcessed_3138_){
_start:
{
lean_object* v_result_x3f_3140_; 
v_result_x3f_3140_ = lean_ctor_get(v_oldProcessed_3138_, 2);
if (lean_obj_tag(v_result_x3f_3140_) == 1)
{
lean_object* v_val_3141_; lean_object* v_firstCmdSnap_3142_; lean_object* v_toSnapshot_3143_; lean_object* v_cmdState_3144_; lean_object* v_stx_x3f_3145_; lean_object* v___f_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; 
v_val_3141_ = lean_ctor_get(v_result_x3f_3140_, 0);
lean_inc(v_val_3141_);
v_firstCmdSnap_3142_ = lean_ctor_get(v_val_3141_, 1);
lean_inc_ref(v_firstCmdSnap_3142_);
v_toSnapshot_3143_ = lean_ctor_get(v_oldProcessed_3138_, 0);
lean_inc_ref(v_toSnapshot_3143_);
lean_dec_ref(v_oldProcessed_3138_);
v_cmdState_3144_ = lean_ctor_get(v_val_3141_, 0);
lean_inc_ref(v_cmdState_3144_);
lean_dec(v_val_3141_);
v_stx_x3f_3145_ = lean_ctor_get(v_firstCmdSnap_3142_, 0);
lean_inc(v_stx_x3f_3145_);
lean_inc_ref(v_a_3135_);
v___f_3146_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3146_, 0, v_newParserState_3134_);
lean_closure_set(v___f_3146_, 1, v_cmdState_3144_);
lean_closure_set(v___f_3146_, 2, v_a_3135_);
lean_closure_set(v___f_3146_, 3, v_toSnapshot_3143_);
lean_closure_set(v___f_3146_, 4, v_newStx_3136_);
v___x_3147_ = lean_box(0);
v___x_3148_ = 1;
v___x_3149_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3142_, v___f_3146_, v_stx_x3f_3145_, v___x_3137_, v___x_3147_, v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v___x_3137_);
lean_dec_ref(v_newParserState_3134_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_newStx_3136_);
v___x_3151_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3150_, v_oldProcessed_3138_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3152_, lean_object* v_a_3153_, lean_object* v_newStx_3154_, lean_object* v___x_3155_, lean_object* v_oldProcessed_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3152_, v_a_3153_, v_newStx_3154_, v___x_3155_, v_oldProcessed_3156_);
lean_dec_ref(v_a_3153_);
return v_res_3158_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3159_ = 0;
v___x_3160_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3161_ = lean_box(0);
v___x_3162_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3163_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3164_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3162_);
lean_ctor_set(v___x_3164_, 2, v___x_3161_);
lean_ctor_set(v___x_3164_, 3, v___x_3160_);
lean_ctor_set_uint8(v___x_3164_, sizeof(void*)*4, v___x_3159_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3165_, lean_object* v_a_3166_, lean_object* v_old_3167_, lean_object* v_newStx_3168_, lean_object* v_newParserState_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_result_x3f_3172_; 
v_result_x3f_3172_ = lean_ctor_get(v_old_3167_, 4);
lean_inc(v_result_x3f_3172_);
if (lean_obj_tag(v_result_x3f_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3227_; 
v_val_3173_ = lean_ctor_get(v_result_x3f_3172_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_result_x3f_3172_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3175_ = v_result_x3f_3172_;
v_isShared_3176_ = v_isSharedCheck_3227_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_val_3173_);
lean_dec(v_result_x3f_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3227_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_processedSnap_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3225_; 
v_processedSnap_3177_ = lean_ctor_get(v_val_3173_, 1);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_val_3173_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v_val_3173_, 0);
lean_dec(v_unused_3226_);
v___x_3179_ = v_val_3173_;
v_isShared_3180_ = v_isSharedCheck_3225_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_processedSnap_3177_);
lean_dec(v_val_3173_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3225_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_toSnapshot_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3220_; 
v_toSnapshot_3181_ = lean_ctor_get(v_old_3167_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_old_3167_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; lean_object* v_unused_3222_; lean_object* v_unused_3223_; lean_object* v_unused_3224_; 
v_unused_3221_ = lean_ctor_get(v_old_3167_, 4);
lean_dec(v_unused_3221_);
v_unused_3222_ = lean_ctor_get(v_old_3167_, 3);
lean_dec(v_unused_3222_);
v_unused_3223_ = lean_ctor_get(v_old_3167_, 2);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_old_3167_, 1);
lean_dec(v_unused_3224_);
v___x_3183_ = v_old_3167_;
v_isShared_3184_ = v_isSharedCheck_3220_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_toSnapshot_3181_);
lean_dec(v_old_3167_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3220_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_pos_3185_; lean_object* v_endPos_3186_; lean_object* v_stx_x3f_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v_diagnostics_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3216_; 
v_pos_3185_ = lean_ctor_get(v_newParserState_3169_, 0);
v_endPos_3186_ = lean_ctor_get(v_toProcessingContext_3165_, 3);
v_stx_x3f_3187_ = lean_ctor_get(v_processedSnap_3177_, 0);
lean_inc(v_stx_x3f_3187_);
lean_inc(v_endPos_3186_);
lean_inc(v_pos_3185_);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_pos_3185_);
lean_ctor_set(v___x_3188_, 1, v_endPos_3186_);
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_inc_ref(v___x_3189_);
lean_inc(v_newStx_3168_);
lean_inc_ref(v_a_3166_);
lean_inc_ref(v_newParserState_3169_);
v___f_3190_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3190_, 0, v_newParserState_3169_);
lean_closure_set(v___f_3190_, 1, v_a_3166_);
lean_closure_set(v___f_3190_, 2, v_newStx_3168_);
lean_closure_set(v___f_3190_, 3, v___x_3189_);
v___x_3191_ = lean_box(0);
v___x_3192_ = 1;
v___x_3193_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3177_, v___f_3190_, v_stx_x3f_3187_, v___x_3189_, v___x_3191_, v___x_3192_);
v_diagnostics_3194_ = lean_ctor_get(v_toSnapshot_3181_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_toSnapshot_3181_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3217_ = lean_ctor_get(v_toSnapshot_3181_, 3);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_toSnapshot_3181_, 2);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_toSnapshot_3181_, 0);
lean_dec(v_unused_3219_);
v___x_3196_ = v_toSnapshot_3181_;
v_isShared_3197_ = v_isSharedCheck_3216_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_diagnostics_3194_);
lean_dec(v_toSnapshot_3181_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3216_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3198_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3199_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v___x_3193_);
lean_ctor_set(v___x_3179_, 0, v_newParserState_3169_);
v___x_3201_ = v___x_3179_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_newParserState_3169_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3193_);
v___x_3201_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3201_);
v___x_3203_ = v___x_3175_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3204_ = 0;
v___x_3205_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3168_);
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_newStx_3168_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 3, v___x_3199_);
lean_ctor_set(v___x_3196_, 2, v___x_3191_);
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3208_ = v___x_3196_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_diagnostics_3194_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v___x_3199_);
v___x_3208_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*4, v___x_3204_);
v___x_3209_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3206_, v___x_3208_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 4, v___x_3203_);
lean_ctor_set(v___x_3183_, 3, v_newStx_3168_);
lean_ctor_set(v___x_3183_, 2, v_toProcessingContext_3165_);
lean_ctor_set(v___x_3183_, 1, v___x_3209_);
lean_ctor_set(v___x_3183_, 0, v___x_3205_);
v___x_3211_ = v___x_3183_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_toProcessingContext_3165_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_newStx_3168_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v___x_3203_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
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
lean_dec(v_result_x3f_3172_);
lean_dec_ref(v_newParserState_3169_);
lean_dec(v_newStx_3168_);
lean_dec_ref(v_toProcessingContext_3165_);
return v_old_3167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3228_, lean_object* v_a_3229_, lean_object* v_old_3230_, lean_object* v_newStx_3231_, lean_object* v_newParserState_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3228_, v_a_3229_, v_old_3230_, v_newStx_3231_, v_newParserState_3232_, v___y_3233_);
lean_dec_ref(v___y_3233_);
lean_dec_ref(v_a_3229_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3236_, lean_object* v_setupImports_3237_, lean_object* v_old_x3f_3238_, lean_object* v___f_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
lean_inc_ref(v_toProcessingContext_3236_);
v___x_3242_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3236_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3312_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3312_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3312_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_snd_3247_; lean_object* v_fst_3248_; lean_object* v_fst_3249_; lean_object* v_snd_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3311_; 
v_snd_3247_ = lean_ctor_get(v_a_3243_, 1);
lean_inc(v_snd_3247_);
v_fst_3248_ = lean_ctor_get(v_a_3243_, 0);
lean_inc(v_fst_3248_);
lean_dec(v_a_3243_);
v_fst_3249_ = lean_ctor_get(v_snd_3247_, 0);
v_snd_3250_ = lean_ctor_get(v_snd_3247_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_snd_3247_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3252_ = v_snd_3247_;
v_isShared_3253_ = v_isSharedCheck_3311_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_snd_3250_);
lean_inc(v_fst_3249_);
lean_dec(v_snd_3247_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3311_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Lean_MessageLog_hasErrors(v_snd_3250_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___y_3257_; 
lean_inc(v_fst_3248_);
v___x_3255_ = l_Lean_Syntax_unsetTrailing(v_fst_3248_);
if (lean_obj_tag(v_old_x3f_3238_) == 1)
{
lean_object* v_val_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3294_; 
v_val_3278_ = lean_ctor_get(v_old_x3f_3238_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_old_x3f_3238_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3280_ = v_old_x3f_3238_;
v_isShared_3281_ = v_isSharedCheck_3294_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_val_3278_);
lean_dec(v_old_x3f_3238_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3294_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_stx_3282_; lean_object* v_result_x3f_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_stx_3282_ = lean_ctor_get(v_val_3278_, 3);
v_result_x3f_3283_ = lean_ctor_get(v_val_3278_, 4);
lean_inc(v_stx_3282_);
v___x_3284_ = l_Lean_Syntax_unsetTrailing(v_stx_3282_);
lean_inc(v___x_3255_);
v___x_3285_ = l_Lean_Syntax_eqWithInfo(v___x_3255_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_inc(v_result_x3f_3283_);
lean_del_object(v___x_3280_);
lean_dec(v_val_3278_);
lean_dec_ref(v___f_3239_);
if (lean_obj_tag(v_result_x3f_3283_) == 0)
{
v___y_3257_ = v___y_3240_;
goto v___jp_3256_;
}
else
{
lean_object* v_val_3286_; lean_object* v_processedSnap_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_val_3286_ = lean_ctor_get(v_result_x3f_3283_, 0);
lean_inc(v_val_3286_);
lean_dec_ref(v_result_x3f_3283_);
v_processedSnap_3287_ = lean_ctor_get(v_val_3286_, 1);
lean_inc_ref(v_processedSnap_3287_);
lean_dec(v_val_3286_);
v___x_3288_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3289_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3288_, v_processedSnap_3287_);
v___y_3257_ = v___y_3240_;
goto v___jp_3256_;
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3292_; 
lean_dec(v___x_3255_);
lean_del_object(v___x_3252_);
lean_dec(v_snd_3250_);
lean_del_object(v___x_3245_);
lean_dec_ref(v_setupImports_3237_);
lean_dec_ref(v_toProcessingContext_3236_);
lean_inc_ref(v___y_3240_);
v___x_3290_ = lean_apply_5(v___f_3239_, v_val_3278_, v_fst_3248_, v_fst_3249_, v___y_3240_, lean_box(0));
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3290_);
v___x_3292_ = v___x_3280_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_dec_ref(v___f_3239_);
lean_dec(v_old_x3f_3238_);
v___y_3257_ = v___y_3240_;
goto v___jp_3256_;
}
v___jp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3258_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3250_);
lean_inc(v_fst_3249_);
v___x_3259_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3237_, v___x_3255_, v_fst_3249_, v___y_3257_);
v___x_3260_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3261_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_unsigned_to_nat(32u);
v___x_3264_ = lean_mk_empty_array_with_capacity(v___x_3263_);
lean_dec_ref(v___x_3264_);
v___x_3265_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v___x_3259_);
v___x_3267_ = v___x_3252_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_fst_3249_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v___x_3259_);
v___x_3267_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3269_, 0, v___x_3260_);
lean_ctor_set(v___x_3269_, 1, v___x_3261_);
lean_ctor_set(v___x_3269_, 2, v___x_3262_);
lean_ctor_set(v___x_3269_, 3, v___x_3265_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*4, v___x_3254_);
lean_inc(v_fst_3248_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_fst_3248_);
v___x_3271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3271_, 0, v___x_3260_);
lean_ctor_set(v___x_3271_, 1, v___x_3258_);
lean_ctor_set(v___x_3271_, 2, v___x_3262_);
lean_ctor_set(v___x_3271_, 3, v___x_3265_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*4, v___x_3254_);
v___x_3272_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3270_, v___x_3271_);
v___x_3273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3269_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
lean_ctor_set(v___x_3273_, 2, v_toProcessingContext_3236_);
lean_ctor_set(v___x_3273_, 3, v_fst_3248_);
lean_ctor_set(v___x_3273_, 4, v___x_3268_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3273_);
v___x_3275_ = v___x_3245_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
lean_del_object(v___x_3252_);
lean_dec(v_fst_3249_);
lean_dec_ref(v___f_3239_);
lean_dec(v_old_x3f_3238_);
lean_dec_ref(v_setupImports_3237_);
v___x_3295_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3250_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3297_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_unsigned_to_nat(32u);
v___x_3300_ = lean_mk_empty_array_with_capacity(v___x_3299_);
lean_dec_ref(v___x_3300_);
v___x_3301_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3302_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3302_, 0, v___x_3296_);
lean_ctor_set(v___x_3302_, 1, v___x_3297_);
lean_ctor_set(v___x_3302_, 2, v___x_3298_);
lean_ctor_set(v___x_3302_, 3, v___x_3301_);
lean_ctor_set_uint8(v___x_3302_, sizeof(void*)*4, v___x_3254_);
lean_inc(v_fst_3248_);
v___x_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_fst_3248_);
v___x_3304_ = 0;
v___x_3305_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3305_, 0, v___x_3296_);
lean_ctor_set(v___x_3305_, 1, v___x_3295_);
lean_ctor_set(v___x_3305_, 2, v___x_3298_);
lean_ctor_set(v___x_3305_, 3, v___x_3301_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*4, v___x_3304_);
v___x_3306_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3303_, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3302_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
lean_ctor_set(v___x_3307_, 2, v_toProcessingContext_3236_);
lean_ctor_set(v___x_3307_, 3, v_fst_3248_);
lean_ctor_set(v___x_3307_, 4, v___x_3298_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3307_);
v___x_3309_ = v___x_3245_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v___f_3239_);
lean_dec(v_old_x3f_3238_);
lean_dec_ref(v_setupImports_3237_);
lean_dec_ref(v_toProcessingContext_3236_);
v_a_3313_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3242_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3242_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3321_, lean_object* v_setupImports_3322_, lean_object* v_old_x3f_3323_, lean_object* v___f_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3321_, v_setupImports_3322_, v_old_x3f_3323_, v___f_3324_, v___y_3325_);
lean_dec_ref(v___y_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3328_, lean_object* v_toProcessingContext_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3331_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3328_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3334_, 0, v_x_3330_);
lean_ctor_set(v___x_3334_, 1, v___x_3331_);
lean_ctor_set(v___x_3334_, 2, v_toProcessingContext_3329_);
lean_ctor_set(v___x_3334_, 3, v___x_3332_);
lean_ctor_set(v___x_3334_, 4, v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3335_, lean_object* v_old_x3f_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_toProcessingContext_3339_; lean_object* v___x_3340_; lean_object* v___f_3341_; lean_object* v___f_3342_; lean_object* v___f_3343_; 
v_toProcessingContext_3339_ = lean_ctor_get(v_a_3337_, 0);
v___x_3340_ = l_Lean_Language_instInhabitedSnapshot_default;
lean_inc_ref(v_a_3337_);
lean_inc_ref_n(v_toProcessingContext_3339_, 3);
v___f_3341_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3341_, 0, v_toProcessingContext_3339_);
lean_closure_set(v___f_3341_, 1, v_a_3337_);
lean_inc(v_old_x3f_3336_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3342_, 0, v_toProcessingContext_3339_);
lean_closure_set(v___f_3342_, 1, v_setupImports_3335_);
lean_closure_set(v___f_3342_, 2, v_old_x3f_3336_);
lean_closure_set(v___f_3342_, 3, v___f_3341_);
v___f_3343_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3343_, 0, v___x_3340_);
lean_closure_set(v___f_3343_, 1, v_toProcessingContext_3339_);
if (lean_obj_tag(v_old_x3f_3336_) == 1)
{
lean_object* v_val_3344_; lean_object* v_result_x3f_3345_; 
v_val_3344_ = lean_ctor_get(v_old_x3f_3336_, 0);
lean_inc(v_val_3344_);
lean_dec_ref(v_old_x3f_3336_);
v_result_x3f_3345_ = lean_ctor_get(v_val_3344_, 4);
if (lean_obj_tag(v_result_x3f_3345_) == 1)
{
lean_object* v_stx_3346_; lean_object* v_val_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_stx_3346_ = lean_ctor_get(v_val_3344_, 3);
lean_inc(v_stx_3346_);
v_val_3347_ = lean_ctor_get(v_result_x3f_3345_, 0);
lean_inc(v_val_3344_);
v___x_3348_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3344_);
v___x_3349_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3348_);
if (lean_obj_tag(v___x_3349_) == 1)
{
lean_object* v_val_3350_; 
v_val_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_val_3350_);
lean_dec_ref(v___x_3349_);
if (lean_obj_tag(v_val_3350_) == 1)
{
lean_object* v_val_3351_; lean_object* v_firstCmdSnap_3352_; lean_object* v___x_3353_; 
v_val_3351_ = lean_ctor_get(v_val_3350_, 0);
lean_inc(v_val_3351_);
lean_dec_ref(v_val_3350_);
v_firstCmdSnap_3352_ = lean_ctor_get(v_val_3351_, 1);
lean_inc_ref(v_firstCmdSnap_3352_);
lean_dec(v_val_3351_);
v___x_3353_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3352_);
if (lean_obj_tag(v___x_3353_) == 1)
{
lean_object* v_val_3354_; lean_object* v_nextCmdSnap_x3f_3355_; 
v_val_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_val_3354_);
lean_dec_ref(v___x_3353_);
v_nextCmdSnap_x3f_3355_ = lean_ctor_get(v_val_3354_, 4);
lean_inc(v_nextCmdSnap_x3f_3355_);
lean_dec(v_val_3354_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3356_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3356_;
}
else
{
lean_object* v_val_3357_; lean_object* v___x_3358_; 
v_val_3357_ = lean_ctor_get(v_nextCmdSnap_x3f_3355_, 0);
lean_inc(v_val_3357_);
lean_dec_ref(v_nextCmdSnap_x3f_3355_);
v___x_3358_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3357_);
if (lean_obj_tag(v___x_3358_) == 1)
{
lean_object* v_val_3359_; lean_object* v_parserState_3360_; lean_object* v_pos_3361_; uint8_t v___x_3362_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref(v___x_3358_);
v_parserState_3360_ = lean_ctor_get(v_val_3359_, 2);
lean_inc_ref(v_parserState_3360_);
lean_dec(v_val_3359_);
v_pos_3361_ = lean_ctor_get(v_parserState_3360_, 0);
lean_inc(v_pos_3361_);
lean_dec_ref(v_parserState_3360_);
v___x_3362_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3361_, v_a_3337_);
lean_dec(v_pos_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3363_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3363_;
}
else
{
lean_object* v_parserState_3364_; lean_object* v___x_3365_; 
lean_dec_ref(v___f_3343_);
lean_dec_ref(v___f_3342_);
v_parserState_3364_ = lean_ctor_get(v_val_3347_, 0);
lean_inc_ref(v_parserState_3364_);
lean_inc_ref(v_toProcessingContext_3339_);
v___x_3365_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3339_, v_a_3337_, v_val_3344_, v_stx_3346_, v_parserState_3364_, v_a_3337_);
return v___x_3365_;
}
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3358_);
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3366_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3366_;
}
}
}
else
{
lean_object* v___x_3367_; 
lean_dec(v___x_3353_);
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3367_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3367_;
}
}
else
{
lean_object* v___x_3368_; 
lean_dec(v_val_3350_);
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3368_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3368_;
}
}
else
{
lean_object* v___x_3369_; 
lean_dec(v___x_3349_);
lean_dec(v_stx_3346_);
lean_dec(v_val_3344_);
v___x_3369_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3369_;
}
}
else
{
lean_object* v___x_3370_; 
lean_dec(v_val_3344_);
v___x_3370_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3370_;
}
}
else
{
lean_object* v___x_3371_; 
lean_dec(v_old_x3f_3336_);
v___x_3371_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3343_, v___f_3342_, v_a_3337_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3372_, lean_object* v_old_x3f_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3372_, v_old_x3f_3373_, v_a_3374_);
lean_dec_ref(v_a_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3377_, lean_object* v_old_x3f_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; 
lean_inc(v_old_x3f_3378_);
v___x_3381_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3381_, 0, v_setupImports_3377_);
lean_closure_set(v___x_3381_, 1, v_old_x3f_3378_);
if (lean_obj_tag(v_old_x3f_3378_) == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = lean_box(0);
v___x_3383_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3381_, v___x_3382_, v_a_3379_);
return v___x_3383_;
}
else
{
lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3393_; 
v_val_3384_ = lean_ctor_get(v_old_x3f_3378_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_old_x3f_3378_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3386_ = v_old_x3f_3378_;
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v_old_x3f_3378_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_ictx_3388_; lean_object* v___x_3390_; 
v_ictx_3388_ = lean_ctor_get(v_val_3384_, 2);
lean_inc_ref(v_ictx_3388_);
lean_dec(v_val_3384_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v_ictx_3388_);
v___x_3390_ = v___x_3386_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_ictx_3388_);
v___x_3390_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3381_, v___x_3390_, v_a_3379_);
return v___x_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3394_, lean_object* v_old_x3f_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Language_Lean_process(v_setupImports_3394_, v_old_x3f_3395_, v_a_3396_);
lean_dec_ref(v_a_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3399_, lean_object* v_parserState_3400_, lean_object* v_commandState_3401_, lean_object* v_old_x3f_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3412_; 
v___x_3404_ = lean_io_promise_new();
v___x_3405_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3402_) == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_box(0);
v___y_3412_ = v___x_3426_;
goto v___jp_3411_;
}
else
{
lean_object* v_val_3427_; lean_object* v_snd_3428_; lean_object* v___x_3429_; 
v_val_3427_ = lean_ctor_get(v_old_x3f_3402_, 0);
v_snd_3428_ = lean_ctor_get(v_val_3427_, 1);
lean_inc(v_snd_3428_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_snd_3428_);
v___y_3412_ = v___x_3429_;
goto v___jp_3411_;
}
v___jp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3407_, v___y_3408_, v_inputCtx_3399_);
lean_dec(v___x_3409_);
v___x_3410_ = l_IO_Promise_result_x21___redArg(v___x_3404_);
lean_dec(v___x_3404_);
return v___x_3410_;
}
v___jp_3411_:
{
uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = 1;
v___x_3414_ = lean_box(v___x_3413_);
lean_inc(v___x_3404_);
v___x_3415_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3415_, 0, v___y_3412_);
lean_closure_set(v___x_3415_, 1, v_parserState_3400_);
lean_closure_set(v___x_3415_, 2, v_commandState_3401_);
lean_closure_set(v___x_3415_, 3, v___x_3404_);
lean_closure_set(v___x_3415_, 4, v___x_3414_);
lean_closure_set(v___x_3415_, 5, v___x_3405_);
if (lean_obj_tag(v_old_x3f_3402_) == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_box(0);
v___y_3407_ = v___x_3415_;
v___y_3408_ = v___x_3416_;
goto v___jp_3406_;
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3425_; 
v_val_3417_ = lean_ctor_get(v_old_x3f_3402_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_old_x3f_3402_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3419_ = v_old_x3f_3402_;
v_isShared_3420_ = v_isSharedCheck_3425_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_old_x3f_3402_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3425_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; lean_object* v___x_3423_; 
v_fst_3421_ = lean_ctor_get(v_val_3417_, 0);
lean_inc(v_fst_3421_);
lean_dec(v_val_3417_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_fst_3421_);
v___x_3423_ = v___x_3419_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_fst_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
v___y_3407_ = v___x_3415_;
v___y_3408_ = v___x_3423_;
goto v___jp_3406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3430_, lean_object* v_parserState_3431_, lean_object* v_commandState_3432_, lean_object* v_old_x3f_3433_, lean_object* v_a_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3430_, v_parserState_3431_, v_commandState_3432_, v_old_x3f_3433_);
lean_dec_ref(v_inputCtx_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3436_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3437_; 
v_nextCmdSnap_x3f_3437_ = lean_ctor_get(v_snap_3436_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3437_) == 1)
{
lean_object* v_val_3438_; lean_object* v___x_3439_; 
lean_inc_ref(v_nextCmdSnap_x3f_3437_);
lean_dec_ref(v_snap_3436_);
v_val_3438_ = lean_ctor_get(v_nextCmdSnap_x3f_3437_, 0);
lean_inc(v_val_3438_);
lean_dec_ref(v_nextCmdSnap_x3f_3437_);
v___x_3439_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3438_);
v_snap_3436_ = v___x_3439_;
goto _start;
}
else
{
lean_object* v_elabSnap_3441_; lean_object* v_resultSnap_3442_; lean_object* v___x_3443_; lean_object* v_cmdState_3444_; lean_object* v___x_3445_; 
v_elabSnap_3441_ = lean_ctor_get(v_snap_3436_, 3);
lean_inc_ref(v_elabSnap_3441_);
lean_dec_ref(v_snap_3436_);
v_resultSnap_3442_ = lean_ctor_get(v_elabSnap_3441_, 2);
lean_inc_ref(v_resultSnap_3442_);
lean_dec_ref(v_elabSnap_3441_);
v___x_3443_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3442_);
v_cmdState_3444_ = lean_ctor_get(v___x_3443_, 1);
lean_inc_ref(v_cmdState_3444_);
lean_dec(v___x_3443_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_cmdState_3444_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3446_){
_start:
{
lean_object* v_result_x3f_3447_; 
v_result_x3f_3447_ = lean_ctor_get(v_snap_3446_, 4);
lean_inc(v_result_x3f_3447_);
lean_dec_ref(v_snap_3446_);
if (lean_obj_tag(v_result_x3f_3447_) == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_box(0);
return v___x_3448_;
}
else
{
lean_object* v_val_3449_; lean_object* v_processedSnap_3450_; lean_object* v___x_3451_; lean_object* v_result_x3f_3452_; 
v_val_3449_ = lean_ctor_get(v_result_x3f_3447_, 0);
lean_inc(v_val_3449_);
lean_dec_ref(v_result_x3f_3447_);
v_processedSnap_3450_ = lean_ctor_get(v_val_3449_, 1);
lean_inc_ref(v_processedSnap_3450_);
lean_dec(v_val_3449_);
v___x_3451_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3450_);
v_result_x3f_3452_ = lean_ctor_get(v___x_3451_, 2);
lean_inc(v_result_x3f_3452_);
lean_dec(v___x_3451_);
if (lean_obj_tag(v_result_x3f_3452_) == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_box(0);
return v___x_3453_;
}
else
{
lean_object* v_val_3454_; lean_object* v_firstCmdSnap_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_val_3454_ = lean_ctor_get(v_result_x3f_3452_, 0);
lean_inc(v_val_3454_);
lean_dec_ref(v_result_x3f_3452_);
v_firstCmdSnap_3455_ = lean_ctor_get(v_val_3454_, 1);
lean_inc_ref(v_firstCmdSnap_3455_);
lean_dec(v_val_3454_);
v___x_3456_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3455_);
v___x_3457_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3456_);
return v___x_3457_;
}
}
}
}
lean_object* runtime_initialize_Lean_Language_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Language_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_Lean_experimental_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_Lean_experimental_module);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Lean(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Util(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Lean(builtin);
}
#ifdef __cplusplus
}
#endif

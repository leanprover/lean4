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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Language_Lean_reparseOptions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "weak"};
static const lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Language_Lean_reparseOptions___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 5, 49, 232, 223, 147, 119, 138)}};
static const lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___closed__1 = (const lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__1_value;
static const lean_string_object l_Lean_Language_Lean_reparseOptions___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "invalid -D parameter, unknown configuration option '"};
static const lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___closed__2 = (const lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__2_value;
static const lean_string_object l_Lean_Language_Lean_reparseOptions___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "'\n\nIf the option is defined in a library, use '-D"};
static const lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___closed__3 = (const lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__3_value;
static const lean_string_object l_Lean_Language_Lean_reparseOptions___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' to set it conditionally"};
static const lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___closed__4 = (const lean_object*)&l_Lean_Language_Lean_reparseOptions___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
v___x_65_ = lean_nat_dec_lt(v_pos_59_, v_val_64_);
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
lean_dec_ref(v_a_119_);
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
lean_inc_ref(v_toProcessingContext_124_);
lean_dec_ref(v_a_119_);
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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___lam__0(lean_object* v_a_315_, lean_object* v_x_316_, lean_object* v_____s_317_){
_start:
{
lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_fst_319_ = lean_ctor_get(v_x_316_, 0);
lean_inc(v_fst_319_);
v_snd_320_ = lean_ctor_get(v_x_316_, 1);
lean_inc(v_snd_320_);
lean_dec_ref(v_x_316_);
v___x_321_ = l_Lean_Name_getRoot(v_fst_319_);
v___x_322_ = ((lean_object*)(l_Lean_Language_Lean_reparseOptions___lam__0___closed__1));
v___x_323_ = lean_box(0);
v___x_324_ = l_Lean_Name_replacePrefix(v_fst_319_, v___x_322_, v___x_323_);
v___x_325_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_315_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_dec(v___x_321_);
if (lean_obj_tag(v_snd_320_) == 0)
{
lean_object* v_val_326_; lean_object* v_v_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_351_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v___x_325_);
v_v_327_ = lean_ctor_get(v_snd_320_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_snd_320_);
if (v_isSharedCheck_351_ == 0)
{
v___x_329_ = v_snd_320_;
v_isShared_330_ = v_isSharedCheck_351_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_v_327_);
lean_dec(v_snd_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_351_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Language_Lean_setOption(v_____s_317_, v_val_326_, v___x_324_, v_v_327_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_342_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_342_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 1);
lean_ctor_set(v___x_329_, 0, v_a_332_);
v___x_337_ = v___x_329_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_del_object(v___x_329_);
v_a_343_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_331_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_331_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
else
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_360_; 
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_325_, 0);
lean_dec(v_unused_361_);
v___x_353_ = v___x_325_;
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
else
{
lean_dec(v___x_325_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_____s_317_, v___x_324_, v_snd_320_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
else
{
uint8_t v___x_362_; 
lean_dec(v___x_325_);
lean_dec(v_snd_320_);
v___x_362_ = lean_name_eq(v___x_321_, v___x_322_);
lean_dec(v___x_321_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec_ref(v_____s_317_);
v___x_363_ = ((lean_object*)(l_Lean_Language_Lean_reparseOptions___lam__0___closed__2));
v___x_364_ = 1;
lean_inc(v___x_324_);
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_324_, v___x_364_);
v___x_366_ = lean_string_append(v___x_363_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l_Lean_Language_Lean_reparseOptions___lam__0___closed__3));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = l_Lean_Name_append(v___x_322_, v___x_324_);
v___x_370_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_369_, v___x_364_);
v___x_371_ = lean_string_append(v___x_368_, v___x_370_);
lean_dec_ref(v___x_370_);
v___x_372_ = ((lean_object*)(l_Lean_Language_Lean_reparseOptions___lam__0___closed__4));
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
v___x_374_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v___x_324_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_____s_317_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___lam__0___boxed(lean_object* v_a_378_, lean_object* v_x_379_, lean_object* v_____s_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Language_Lean_reparseOptions___lam__0(v_a_378_, v_x_379_, v_____s_380_);
lean_dec(v_a_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(lean_object* v_f_383_, lean_object* v_init_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_d_388_; 
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_l_393_; lean_object* v_r_394_; lean_object* v___x_395_; 
v_k_391_ = lean_ctor_get(v_x_385_, 1);
v_v_392_ = lean_ctor_get(v_x_385_, 2);
v_l_393_ = lean_ctor_get(v_x_385_, 3);
v_r_394_ = lean_ctor_get(v_x_385_, 4);
lean_inc_ref(v_f_383_);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(v_f_383_, v_init_384_, v_l_393_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref(v___x_395_);
if (lean_obj_tag(v_a_396_) == 0)
{
lean_object* v_a_397_; 
lean_dec_ref(v_f_383_);
v_a_397_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v_a_396_);
v_d_388_ = v_a_397_;
goto v___jp_387_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v_a_396_);
lean_inc(v_v_392_);
lean_inc(v_k_391_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_k_391_);
lean_ctor_set(v___x_399_, 1, v_v_392_);
lean_inc_ref(v_f_383_);
v___x_400_ = lean_apply_3(v_f_383_, v___x_399_, v_a_398_, lean_box(0));
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
if (lean_obj_tag(v_a_401_) == 0)
{
lean_object* v_a_402_; 
lean_dec_ref(v_f_383_);
v_a_402_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v_a_401_);
v_d_388_ = v_a_402_;
goto v___jp_387_;
}
else
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v_a_401_);
v_init_384_ = v_a_403_;
v_x_385_ = v_r_394_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_383_);
return v___x_400_;
}
}
}
else
{
lean_dec_ref(v_f_383_);
return v___x_395_;
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref(v_f_383_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_init_384_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_d_388_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg___boxed(lean_object* v_f_407_, lean_object* v_init_408_, lean_object* v_x_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(v_f_407_, v_init_408_, v_x_409_);
lean_dec(v_x_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg(lean_object* v_o_412_, lean_object* v_init_413_, lean_object* v_f_414_){
_start:
{
lean_object* v_map_416_; lean_object* v___x_417_; 
v_map_416_ = lean_ctor_get(v_o_412_, 0);
v___x_417_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(v_f_414_, v_init_413_, v_map_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_a_422_; lean_object* v___x_424_; 
v_a_422_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_a_422_);
lean_dec(v_a_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_a_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_417_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg___boxed(lean_object* v_o_435_, lean_object* v_init_436_, lean_object* v_f_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg(v_o_435_, v_init_436_, v_f_437_);
lean_dec_ref(v_o_435_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___f_444_; lean_object* v_opts_x27_445_; lean_object* v___x_446_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_reparseOptions___lam__0___boxed), 4, 1);
lean_closure_set(v___f_444_, 0, v_a_443_);
v_opts_x27_445_ = l_Lean_Options_empty;
v___x_446_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg(v_opts_440_, v_opts_x27_445_, v___f_444_);
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_442_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_442_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Language_Lean_reparseOptions(v_opts_455_);
lean_dec_ref(v_opts_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object* v_00_u03b2_458_, lean_object* v_o_459_, lean_object* v_init_460_, lean_object* v_f_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___redArg(v_o_459_, v_init_460_, v_f_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_00_u03b2_464_, lean_object* v_o_465_, lean_object* v_init_466_, lean_object* v_f_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1(v_00_u03b2_464_, v_o_465_, v_init_466_, v_f_467_);
lean_dec_ref(v_o_465_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_f_471_, lean_object* v_init_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___redArg(v_f_471_, v_init_472_, v_x_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1___boxed(lean_object* v_00_u03b2_476_, lean_object* v_f_477_, lean_object* v_init_478_, lean_object* v_x_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_Language_Lean_reparseOptions_spec__1_spec__1(v_00_u03b2_476_, v_f_477_, v_init_478_, v_x_479_);
lean_dec(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_490_){
_start:
{
lean_object* v_stx_492_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = l_Lean_Syntax_getArg(v_stx_490_, v___x_495_);
v___x_497_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_498_ = l_Lean_Syntax_isOfKind(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
v_stx_492_ = v_stx_490_;
goto v___jp_491_;
}
else
{
lean_object* v___x_499_; lean_object* v_stx_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v_stx_500_ = l_Lean_Syntax_getArg(v_stx_490_, v___x_499_);
lean_dec(v_stx_490_);
v_stx_492_ = v_stx_500_;
goto v___jp_491_;
}
v___jp_491_:
{
uint8_t v___x_493_; lean_object* v___x_494_; 
v___x_493_ = 0;
v___x_494_ = l_Lean_Syntax_getPos_x3f(v_stx_492_, v___x_493_);
lean_dec(v_stx_492_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_501_, lean_object* v_decl_502_, lean_object* v_ref_503_){
_start:
{
lean_object* v_defValue_505_; lean_object* v_descr_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_533_; 
v_defValue_505_ = lean_ctor_get(v_decl_502_, 0);
v_descr_506_ = lean_ctor_get(v_decl_502_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_decl_502_);
if (v_isSharedCheck_533_ == 0)
{
v___x_508_ = v_decl_502_;
v_isShared_509_ = v_isSharedCheck_533_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_descr_506_);
lean_inc(v_defValue_505_);
lean_dec(v_decl_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_533_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_alloc_ctor(1, 0, 1);
v___x_511_ = lean_unbox(v_defValue_505_);
lean_ctor_set_uint8(v___x_510_, 0, v___x_511_);
lean_inc(v_name_501_);
v___x_512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_512_, 0, v_name_501_);
lean_ctor_set(v___x_512_, 1, v_ref_503_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v_descr_506_);
lean_inc(v_name_501_);
v___x_513_ = lean_register_option(v_name_501_, v___x_512_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_524_);
v___x_515_ = v___x_513_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_dec(v___x_513_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_defValue_505_);
lean_ctor_set(v___x_508_, 0, v_name_501_);
v___x_518_ = v___x_508_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_name_501_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_defValue_505_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_508_);
lean_dec(v_defValue_505_);
lean_dec(v_name_501_);
v_a_525_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_513_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_513_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_534_, lean_object* v_decl_535_, lean_object* v_ref_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_534_, v_decl_535_, v_ref_536_);
return v_res_538_;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_550_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_551_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_552_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_553_ = l_Lean_Name_mkStr5(v___x_552_, v___x_551_, v___x_552_, v___x_550_, v___x_549_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_556_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_557_ = lean_obj_once(&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_, &l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__once, _init_l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_);
v___x_558_ = l_Lean_Option_register___at___00Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_555_, v___x_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(32u);
v___x_562_ = lean_mk_empty_array_with_capacity(v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_564_ = ((size_t)5ULL);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_unsigned_to_nat(32u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_569_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_565_);
lean_ctor_set(v___x_569_, 3, v___x_565_);
lean_ctor_set_usize(v___x_569_, 4, v___x_564_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_infoState_573_; lean_object* v_trees_574_; lean_object* v___x_575_; lean_object* v_infoState_576_; lean_object* v_env_577_; lean_object* v_messages_578_; lean_object* v_scopes_579_; lean_object* v_usedQuotCtxts_580_; lean_object* v_nextMacroScope_581_; lean_object* v_maxRecDepth_582_; lean_object* v_ngen_583_; lean_object* v_auxDeclNGen_584_; lean_object* v_traceState_585_; lean_object* v_snapshotTasks_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_607_; 
v___x_572_ = lean_st_ref_get(v___y_570_);
v_infoState_573_ = lean_ctor_get(v___x_572_, 8);
lean_inc_ref(v_infoState_573_);
lean_dec(v___x_572_);
v_trees_574_ = lean_ctor_get(v_infoState_573_, 2);
lean_inc_ref(v_trees_574_);
lean_dec_ref(v_infoState_573_);
v___x_575_ = lean_st_ref_take(v___y_570_);
v_infoState_576_ = lean_ctor_get(v___x_575_, 8);
v_env_577_ = lean_ctor_get(v___x_575_, 0);
v_messages_578_ = lean_ctor_get(v___x_575_, 1);
v_scopes_579_ = lean_ctor_get(v___x_575_, 2);
v_usedQuotCtxts_580_ = lean_ctor_get(v___x_575_, 3);
v_nextMacroScope_581_ = lean_ctor_get(v___x_575_, 4);
v_maxRecDepth_582_ = lean_ctor_get(v___x_575_, 5);
v_ngen_583_ = lean_ctor_get(v___x_575_, 6);
v_auxDeclNGen_584_ = lean_ctor_get(v___x_575_, 7);
v_traceState_585_ = lean_ctor_get(v___x_575_, 9);
v_snapshotTasks_586_ = lean_ctor_get(v___x_575_, 10);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_607_ == 0)
{
v___x_588_ = v___x_575_;
v_isShared_589_ = v_isSharedCheck_607_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snapshotTasks_586_);
lean_inc(v_traceState_585_);
lean_inc(v_infoState_576_);
lean_inc(v_auxDeclNGen_584_);
lean_inc(v_ngen_583_);
lean_inc(v_maxRecDepth_582_);
lean_inc(v_nextMacroScope_581_);
lean_inc(v_usedQuotCtxts_580_);
lean_inc(v_scopes_579_);
lean_inc(v_messages_578_);
lean_inc(v_env_577_);
lean_dec(v___x_575_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_607_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint8_t v_enabled_590_; lean_object* v_assignment_591_; lean_object* v_lazyAssignment_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_605_; 
v_enabled_590_ = lean_ctor_get_uint8(v_infoState_576_, sizeof(void*)*3);
v_assignment_591_ = lean_ctor_get(v_infoState_576_, 0);
v_lazyAssignment_592_ = lean_ctor_get(v_infoState_576_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_infoState_576_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_infoState_576_, 2);
lean_dec(v_unused_606_);
v___x_594_ = v_infoState_576_;
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_lazyAssignment_592_);
lean_inc(v_assignment_591_);
lean_dec(v_infoState_576_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 2, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_assignment_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_lazyAssignment_592_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v___x_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_604_, sizeof(void*)*3, v_enabled_590_);
v___x_598_ = v_reuseFailAlloc_604_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 8, v___x_598_);
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_env_577_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_messages_578_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_scopes_579_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_usedQuotCtxts_580_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_nextMacroScope_581_);
lean_ctor_set(v_reuseFailAlloc_603_, 5, v_maxRecDepth_582_);
lean_ctor_set(v_reuseFailAlloc_603_, 6, v_ngen_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 7, v_auxDeclNGen_584_);
lean_ctor_set(v_reuseFailAlloc_603_, 8, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_603_, 9, v_traceState_585_);
lean_ctor_set(v_reuseFailAlloc_603_, 10, v_snapshotTasks_586_);
v___x_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_st_ref_set(v___y_570_, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_trees_574_);
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_608_);
lean_dec(v___y_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_619_, lean_object* v_opt_620_){
_start:
{
lean_object* v_name_621_; lean_object* v_defValue_622_; lean_object* v_map_623_; lean_object* v___x_624_; 
v_name_621_ = lean_ctor_get(v_opt_620_, 0);
v_defValue_622_ = lean_ctor_get(v_opt_620_, 1);
v_map_623_ = lean_ctor_get(v_opts_619_, 0);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_623_, v_name_621_);
if (lean_obj_tag(v___x_624_) == 0)
{
uint8_t v___x_625_; 
v___x_625_ = lean_unbox(v_defValue_622_);
return v___x_625_;
}
else
{
lean_object* v_val_626_; 
v_val_626_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_626_);
lean_dec_ref(v___x_624_);
if (lean_obj_tag(v_val_626_) == 1)
{
uint8_t v_v_627_; 
v_v_627_ = lean_ctor_get_uint8(v_val_626_, 0);
lean_dec_ref(v_val_626_);
return v_v_627_;
}
else
{
uint8_t v___x_628_; 
lean_dec(v_val_626_);
v___x_628_ = lean_unbox(v_defValue_622_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_629_, lean_object* v_opt_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_629_, v_opt_630_);
lean_dec_ref(v_opt_630_);
lean_dec_ref(v_opts_629_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_val_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_639_, lean_object* v_val_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_inc_ref(v_val_640_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_641_, 0, v_val_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_inst_639_);
lean_ctor_set(v___x_642_, 1, v_val_640_);
v___x_643_ = lean_mk_thunk(v___f_641_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_647_);
lean_dec_ref(v___x_649_);
v___x_650_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_645_, v___y_646_, v___y_647_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_651_, v___y_652_, v___y_653_);
return v_res_655_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_656_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_ctor_set(v___x_661_, 2, v___x_660_);
lean_ctor_set(v___x_661_, 3, v___x_659_);
lean_ctor_set(v___x_661_, 4, v___x_659_);
lean_ctor_set(v___x_661_, 5, v___x_659_);
lean_ctor_set(v___x_661_, 6, v___x_659_);
lean_ctor_set(v___x_661_, 7, v___x_659_);
lean_ctor_set(v___x_661_, 8, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(32u);
v___x_663_ = lean_mk_empty_array_with_capacity(v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_665_ = ((size_t)5ULL);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_unsigned_to_nat(32u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_670_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
lean_ctor_set(v___x_670_, 2, v___x_666_);
lean_ctor_set(v___x_670_, 3, v___x_666_);
lean_ctor_set_usize(v___x_670_, 4, v___x_665_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = lean_box(1);
v___x_672_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_673_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_671_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v___x_680_; lean_object* v_scopes_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_opts_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_678_ = lean_st_ref_get(v___y_676_);
v_env_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref(v_env_679_);
lean_dec(v___x_678_);
v___x_680_ = lean_st_ref_get(v___y_676_);
v_scopes_681_ = lean_ctor_get(v___x_680_, 2);
lean_inc(v_scopes_681_);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_683_ = l_List_head_x21___redArg(v___x_682_, v_scopes_681_);
lean_dec(v_scopes_681_);
v_opts_684_ = lean_ctor_get(v___x_683_, 1);
lean_inc_ref(v_opts_684_);
lean_dec(v___x_683_);
v___x_685_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_686_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_687_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_687_, 0, v_env_679_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_ctor_set(v___x_687_, 3, v_opts_684_);
v___x_688_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_msgData_675_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_690_, v___y_691_);
lean_dec(v___y_691_);
return v_res_693_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_694_, uint8_t v_suppressElabErrors_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 1)
{
lean_object* v_pre_697_; 
v_pre_697_ = lean_ctor_get(v_x_696_, 0);
if (lean_obj_tag(v_pre_697_) == 0)
{
lean_object* v_str_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_str_698_ = lean_ctor_get(v_x_696_, 1);
v___x_699_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_700_ = lean_string_dec_eq(v_str_698_, v___x_699_);
if (v___x_700_ == 0)
{
return v___y_694_;
}
else
{
return v_suppressElabErrors_695_;
}
}
else
{
return v___y_694_;
}
}
else
{
return v___y_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_701_, lean_object* v_suppressElabErrors_702_, lean_object* v_x_703_){
_start:
{
uint8_t v___y_10642__boxed_704_; uint8_t v_suppressElabErrors_boxed_705_; uint8_t v_res_706_; lean_object* v_r_707_; 
v___y_10642__boxed_704_ = lean_unbox(v___y_701_);
v_suppressElabErrors_boxed_705_ = lean_unbox(v_suppressElabErrors_702_);
v_res_706_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_10642__boxed_704_, v_suppressElabErrors_boxed_705_, v_x_703_);
lean_dec(v_x_703_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_709_, lean_object* v_msgData_710_, uint8_t v_severity_711_, uint8_t v_isSilent_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_780_; uint8_t v___y_781_; uint8_t v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; uint8_t v___y_808_; uint8_t v___y_809_; uint8_t v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; uint8_t v___y_816_; uint8_t v___y_817_; uint8_t v___y_818_; uint8_t v___x_833_; uint8_t v___y_835_; uint8_t v___y_836_; uint8_t v___y_837_; uint8_t v___y_839_; uint8_t v___x_851_; 
v___x_833_ = 2;
v___x_851_ = l_Lean_instBEqMessageSeverity_beq(v_severity_711_, v___x_833_);
if (v___x_851_ == 0)
{
v___y_839_ = v___x_851_;
goto v___jp_838_;
}
else
{
uint8_t v___x_852_; 
lean_inc_ref(v_msgData_710_);
v___x_852_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_710_);
v___y_839_ = v___x_852_;
goto v___jp_838_;
}
v___jp_716_:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Elab_Command_getScope___redArg(v___y_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = l_Lean_Elab_Command_getScope___redArg(v___y_724_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_762_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_762_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_762_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_762_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v_currNamespace_733_; lean_object* v_openDecls_734_; lean_object* v_env_735_; lean_object* v_messages_736_; lean_object* v_scopes_737_; lean_object* v_usedQuotCtxts_738_; lean_object* v_nextMacroScope_739_; lean_object* v_maxRecDepth_740_; lean_object* v_ngen_741_; lean_object* v_auxDeclNGen_742_; lean_object* v_infoState_743_; lean_object* v_traceState_744_; lean_object* v_snapshotTasks_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_761_; 
v___x_732_ = lean_st_ref_take(v___y_724_);
v_currNamespace_733_ = lean_ctor_get(v_a_726_, 2);
lean_inc(v_currNamespace_733_);
lean_dec(v_a_726_);
v_openDecls_734_ = lean_ctor_get(v_a_728_, 3);
lean_inc(v_openDecls_734_);
lean_dec(v_a_728_);
v_env_735_ = lean_ctor_get(v___x_732_, 0);
v_messages_736_ = lean_ctor_get(v___x_732_, 1);
v_scopes_737_ = lean_ctor_get(v___x_732_, 2);
v_usedQuotCtxts_738_ = lean_ctor_get(v___x_732_, 3);
v_nextMacroScope_739_ = lean_ctor_get(v___x_732_, 4);
v_maxRecDepth_740_ = lean_ctor_get(v___x_732_, 5);
v_ngen_741_ = lean_ctor_get(v___x_732_, 6);
v_auxDeclNGen_742_ = lean_ctor_get(v___x_732_, 7);
v_infoState_743_ = lean_ctor_get(v___x_732_, 8);
v_traceState_744_ = lean_ctor_get(v___x_732_, 9);
v_snapshotTasks_745_ = lean_ctor_get(v___x_732_, 10);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_761_ == 0)
{
v___x_747_ = v___x_732_;
v_isShared_748_ = v_isSharedCheck_761_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snapshotTasks_745_);
lean_inc(v_traceState_744_);
lean_inc(v_infoState_743_);
lean_inc(v_auxDeclNGen_742_);
lean_inc(v_ngen_741_);
lean_inc(v_maxRecDepth_740_);
lean_inc(v_nextMacroScope_739_);
lean_inc(v_usedQuotCtxts_738_);
lean_inc(v_scopes_737_);
lean_inc(v_messages_736_);
lean_inc(v_env_735_);
lean_dec(v___x_732_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_761_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_currNamespace_733_);
lean_ctor_set(v___x_749_, 1, v_openDecls_734_);
v___x_750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___y_721_);
v___x_751_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_751_, 0, v___y_722_);
lean_ctor_set(v___x_751_, 1, v___y_720_);
lean_ctor_set(v___x_751_, 2, v___y_723_);
lean_ctor_set(v___x_751_, 3, v___y_718_);
lean_ctor_set(v___x_751_, 4, v___x_750_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5, v___y_719_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5 + 1, v___y_717_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5 + 2, v_isSilent_712_);
v___x_752_ = l_Lean_MessageLog_add(v___x_751_, v_messages_736_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_env_735_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_scopes_737_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_usedQuotCtxts_738_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_nextMacroScope_739_);
lean_ctor_set(v_reuseFailAlloc_760_, 5, v_maxRecDepth_740_);
lean_ctor_set(v_reuseFailAlloc_760_, 6, v_ngen_741_);
lean_ctor_set(v_reuseFailAlloc_760_, 7, v_auxDeclNGen_742_);
lean_ctor_set(v_reuseFailAlloc_760_, 8, v_infoState_743_);
lean_ctor_set(v_reuseFailAlloc_760_, 9, v_traceState_744_);
lean_ctor_set(v_reuseFailAlloc_760_, 10, v_snapshotTasks_745_);
v___x_754_ = v_reuseFailAlloc_760_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_st_ref_set(v___y_724_, v___x_754_);
v___x_756_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_756_);
v___x_758_ = v___x_730_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_726_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v___y_718_);
v_a_763_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_727_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_727_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v___y_718_);
v_a_771_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_725_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_725_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
v___jp_779_:
{
lean_object* v_fileName_785_; lean_object* v_fileMap_786_; uint8_t v_suppressElabErrors_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_fileName_785_ = lean_ctor_get(v___y_713_, 0);
lean_inc_ref(v_fileName_785_);
v_fileMap_786_ = lean_ctor_get(v___y_713_, 1);
lean_inc_ref(v_fileMap_786_);
v_suppressElabErrors_787_ = lean_ctor_get_uint8(v___y_713_, sizeof(void*)*10);
lean_dec_ref(v___y_713_);
v___x_788_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_710_);
v___x_789_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_788_, v___y_714_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v_fileMap_786_);
v___x_794_ = l_Lean_FileMap_toPosition(v_fileMap_786_, v___y_783_);
lean_dec(v___y_783_);
v___x_795_ = l_Lean_FileMap_toPosition(v_fileMap_786_, v___y_784_);
lean_dec(v___y_784_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
v___x_797_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_787_ == 0)
{
lean_del_object(v___x_792_);
v___y_717_ = v___y_781_;
v___y_718_ = v___x_797_;
v___y_719_ = v___y_782_;
v___y_720_ = v___x_794_;
v___y_721_ = v_a_790_;
v___y_722_ = v_fileName_785_;
v___y_723_ = v___x_796_;
v___y_724_ = v___y_714_;
goto v___jp_716_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___f_800_; uint8_t v___x_801_; 
v___x_798_ = lean_box(v___y_780_);
v___x_799_ = lean_box(v_suppressElabErrors_787_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_800_, 0, v___x_798_);
lean_closure_set(v___f_800_, 1, v___x_799_);
lean_inc(v_a_790_);
v___x_801_ = l_Lean_MessageData_hasTag(v___f_800_, v_a_790_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec_ref(v___x_796_);
lean_dec_ref(v___x_794_);
lean_dec(v_a_790_);
lean_dec_ref(v_fileName_785_);
v___x_802_ = lean_box(0);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_802_);
v___x_804_ = v___x_792_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_del_object(v___x_792_);
v___y_717_ = v___y_781_;
v___y_718_ = v___x_797_;
v___y_719_ = v___y_782_;
v___y_720_ = v___x_794_;
v___y_721_ = v_a_790_;
v___y_722_ = v_fileName_785_;
v___y_723_ = v___x_796_;
v___y_724_ = v___y_714_;
goto v___jp_716_;
}
}
}
}
v___jp_807_:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Syntax_getTailPos_x3f(v___y_811_, v___y_810_);
lean_dec(v___y_811_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_inc(v___y_812_);
v___y_780_ = v___y_808_;
v___y_781_ = v___y_809_;
v___y_782_ = v___y_810_;
v___y_783_ = v___y_812_;
v___y_784_ = v___y_812_;
goto v___jp_779_;
}
else
{
lean_object* v_val_814_; 
v_val_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v___x_813_);
v___y_780_ = v___y_808_;
v___y_781_ = v___y_809_;
v___y_782_ = v___y_810_;
v___y_783_ = v___y_812_;
v___y_784_ = v_val_814_;
goto v___jp_779_;
}
}
v___jp_815_:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Elab_Command_getRef___redArg(v___y_713_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_ref_821_; lean_object* v___x_822_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
v_ref_821_ = l_Lean_replaceRef(v_ref_709_, v_a_820_);
lean_dec(v_a_820_);
v___x_822_ = l_Lean_Syntax_getPos_x3f(v_ref_821_, v___y_817_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___y_808_ = v___y_816_;
v___y_809_ = v___y_818_;
v___y_810_ = v___y_817_;
v___y_811_ = v_ref_821_;
v___y_812_ = v___x_823_;
goto v___jp_807_;
}
else
{
lean_object* v_val_824_; 
v_val_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_824_);
lean_dec_ref(v___x_822_);
v___y_808_ = v___y_816_;
v___y_809_ = v___y_818_;
v___y_810_ = v___y_817_;
v___y_811_ = v_ref_821_;
v___y_812_ = v_val_824_;
goto v___jp_807_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___y_713_);
lean_dec_ref(v_msgData_710_);
v_a_825_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_819_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_819_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
v___jp_834_:
{
if (v___y_837_ == 0)
{
v___y_816_ = v___y_835_;
v___y_817_ = v___y_836_;
v___y_818_ = v_severity_711_;
goto v___jp_815_;
}
else
{
v___y_816_ = v___y_835_;
v___y_817_ = v___y_836_;
v___y_818_ = v___x_833_;
goto v___jp_815_;
}
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_object* v___x_840_; lean_object* v_scopes_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_opts_844_; uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_840_ = lean_st_ref_get(v___y_714_);
v_scopes_841_ = lean_ctor_get(v___x_840_, 2);
lean_inc(v_scopes_841_);
lean_dec(v___x_840_);
v___x_842_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_843_ = l_List_head_x21___redArg(v___x_842_, v_scopes_841_);
lean_dec(v_scopes_841_);
v_opts_844_ = lean_ctor_get(v___x_843_, 1);
lean_inc_ref(v_opts_844_);
lean_dec(v___x_843_);
v___x_845_ = 1;
v___x_846_ = l_Lean_instBEqMessageSeverity_beq(v_severity_711_, v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v_opts_844_);
v___y_835_ = v___y_839_;
v___y_836_ = v___y_839_;
v___y_837_ = v___x_846_;
goto v___jp_834_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = l_Lean_warningAsError;
v___x_848_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_844_, v___x_847_);
lean_dec_ref(v_opts_844_);
v___y_835_ = v___y_839_;
v___y_836_ = v___y_839_;
v___y_837_ = v___x_848_;
goto v___jp_834_;
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v___y_713_);
lean_dec_ref(v_msgData_710_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_853_, lean_object* v_msgData_854_, lean_object* v_severity_855_, lean_object* v_isSilent_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_severity_boxed_860_; uint8_t v_isSilent_boxed_861_; lean_object* v_res_862_; 
v_severity_boxed_860_ = lean_unbox(v_severity_855_);
v_isSilent_boxed_861_ = lean_unbox(v_isSilent_856_);
v_res_862_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_853_, v_msgData_854_, v_severity_boxed_860_, v_isSilent_boxed_861_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec(v_ref_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_863_, uint8_t v_severity_864_, uint8_t v_isSilent_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_Command_getRef___redArg(v___y_866_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_870_, v_msgData_863_, v_severity_864_, v_isSilent_865_, v___y_866_, v___y_867_);
lean_dec(v_a_870_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___y_866_);
lean_dec_ref(v_msgData_863_);
v_a_872_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_869_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_880_, lean_object* v_severity_881_, lean_object* v_isSilent_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v_severity_boxed_886_; uint8_t v_isSilent_boxed_887_; lean_object* v_res_888_; 
v_severity_boxed_886_ = lean_unbox(v_severity_881_);
v_isSilent_boxed_887_ = lean_unbox(v_isSilent_882_);
v_res_888_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_880_, v_severity_boxed_886_, v_isSilent_boxed_887_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = 2;
v___x_894_ = 0;
v___x_895_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_889_, v___x_893_, v___x_894_, v___y_890_, v___y_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_901_, lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
v___x_906_ = 2;
v___x_907_ = 0;
v___x_908_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_901_, v_msgData_902_, v___x_906_, v___x_907_, v___y_903_, v___y_904_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_909_, lean_object* v_msgData_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_909_, v_msgData_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec(v_ref_909_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
if (lean_obj_tag(v_ex_918_) == 0)
{
lean_object* v_ref_922_; lean_object* v_msg_923_; lean_object* v___x_924_; 
v_ref_922_ = lean_ctor_get(v_ex_918_, 0);
lean_inc(v_ref_922_);
v_msg_923_ = lean_ctor_get(v_ex_918_, 1);
lean_inc_ref(v_msg_923_);
lean_dec_ref(v_ex_918_);
v___x_924_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_922_, v_msg_923_, v___y_919_, v___y_920_);
lean_dec(v_ref_922_);
return v___x_924_;
}
else
{
lean_object* v_id_925_; uint8_t v___y_927_; uint8_t v___x_949_; 
v_id_925_ = lean_ctor_get(v_ex_918_, 0);
lean_inc(v_id_925_);
v___x_949_ = l_Lean_Elab_isAbortExceptionId(v_id_925_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_Exception_isInterrupt(v_ex_918_);
lean_dec_ref(v_ex_918_);
v___y_927_ = v___x_950_;
goto v___jp_926_;
}
else
{
lean_dec_ref(v_ex_918_);
v___y_927_ = v___x_949_;
goto v___jp_926_;
}
v___jp_926_:
{
if (v___y_927_ == 0)
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_InternalExceptionId_getName(v_id_925_);
lean_dec(v_id_925_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_931_ = l_Lean_MessageData_ofName(v_a_929_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_932_, v___y_919_, v___y_920_);
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_946_; 
v_a_934_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_946_ == 0)
{
v___x_936_ = v___x_928_;
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_ref_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_ref_938_ = lean_ctor_get(v___y_919_, 7);
lean_inc(v_ref_938_);
lean_dec_ref(v___y_919_);
v___x_939_ = lean_io_error_to_string(v_a_934_);
v___x_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = l_Lean_MessageData_ofFormat(v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_ref_938_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_942_);
v___x_944_ = v___x_936_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_id_925_);
lean_dec_ref(v___y_919_);
v___x_947_ = lean_box(0);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
v___x_960_ = lean_apply_3(v_x_956_, v___y_957_, v___y_958_, lean_box(0));
if (lean_obj_tag(v___x_960_) == 0)
{
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v___x_960_;
}
else
{
lean_object* v_a_961_; uint8_t v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
v___x_962_ = l_Lean_Exception_isInterrupt(v_a_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec_ref(v___x_960_);
v___x_963_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_961_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
return v___x_963_;
}
else
{
lean_dec(v_a_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_964_, v___y_965_, v___y_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_969_, lean_object* v___x_970_, lean_object* v_val_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_a_975_; lean_object* v___x_977_; 
v___x_977_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_969_, v___x_970_, v_val_971_);
if (lean_obj_tag(v___x_977_) == 0)
{
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v_a_975_ = v_a_978_;
goto v___jp_974_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_977_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v___x_987_; 
lean_dec_ref(v___x_977_);
v___x_987_ = lean_box(0);
v_a_975_ = v___x_987_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_a_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_988_, lean_object* v___x_989_, lean_object* v_val_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_988_, v___x_989_, v_val_990_, v___y_991_);
lean_dec_ref(v___y_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_994_, lean_object* v_x_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_get_set_stderr(v_h_994_);
v___x_999_ = lean_apply_2(v_x_995_, v___y_996_, lean_box(0));
v___x_1000_ = lean_get_set_stderr(v___x_998_);
lean_dec_ref(v___x_1000_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_1001_, v_x_1002_, v___y_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_1006_, lean_object* v_h_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_1007_, v_x_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_h_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_1012_, v_h_1013_, v_x_1014_, v___y_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_get_set_stdin(v_h_1018_);
v___x_1023_ = lean_apply_2(v_x_1019_, v___y_1020_, lean_box(0));
v___x_1024_ = lean_get_set_stdin(v___x_1022_);
lean_dec_ref(v___x_1024_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_1025_, lean_object* v_x_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1025_, v_x_1026_, v___y_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1032_ = lean_panic_fn(v___x_1031_, v_msg_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_get_set_stdout(v_h_1033_);
v___x_1038_ = lean_apply_2(v_x_1034_, v___y_1035_, lean_box(0));
v___x_1039_ = lean_get_set_stdout(v___x_1037_);
lean_dec_ref(v___x_1039_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1040_, v_x_1041_, v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_1045_, lean_object* v_h_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1046_, v_x_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_h_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1051_, v_h_1052_, v_x_1053_, v___y_1054_);
return v_res_1056_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = l_ByteArray_empty;
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1063_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1064_ = lean_unsigned_to_nat(46u);
v___x_1065_ = lean_unsigned_to_nat(193u);
v___x_1066_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1067_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1068_ = l_mkPanicMessageWithDecl(v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_, v___x_1063_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1069_, uint8_t v_isolateStderr_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___y_1083_; 
v___x_1077_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1078_ = lean_st_mk_ref(v___x_1077_);
v___x_1079_ = lean_st_mk_ref(v___x_1077_);
v___x_1080_ = l_IO_FS_Stream_ofBuffer(v___x_1078_);
lean_inc(v___x_1079_);
v___x_1081_ = l_IO_FS_Stream_ofBuffer(v___x_1079_);
if (v_isolateStderr_1070_ == 0)
{
v___y_1083_ = v_x_1069_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1092_; 
lean_inc_ref(v___x_1081_);
v___x_1092_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1092_, 0, lean_box(0));
lean_closure_set(v___x_1092_, 1, v___x_1081_);
lean_closure_set(v___x_1092_, 2, v_x_1069_);
v___y_1083_ = v___x_1092_;
goto v___jp_1082_;
}
v___jp_1073_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1075_);
lean_ctor_set(v___x_1076_, 1, v___y_1074_);
return v___x_1076_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_data_1087_; uint8_t v___x_1088_; 
v___x_1084_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1084_, 0, lean_box(0));
lean_closure_set(v___x_1084_, 1, v___x_1081_);
lean_closure_set(v___x_1084_, 2, v___y_1083_);
v___x_1085_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1080_, v___x_1084_, v___y_1071_);
v___x_1086_ = lean_st_ref_get(v___x_1079_);
lean_dec(v___x_1079_);
v_data_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_data_1087_);
lean_dec(v___x_1086_);
v___x_1088_ = lean_string_validate_utf8(v_data_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v_data_1087_);
v___x_1089_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1090_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1089_);
v___y_1074_ = v___x_1085_;
v___y_1075_ = v___x_1090_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_string_from_utf8_unchecked(v_data_1087_);
v___y_1074_ = v___x_1085_;
v___y_1075_ = v___x_1091_;
goto v___jp_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1093_, lean_object* v_isolateStderr_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_isolateStderr_boxed_1097_; lean_object* v_res_1098_; 
v_isolateStderr_boxed_1097_ = lean_unbox(v_isolateStderr_1094_);
v_res_1098_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1093_, v_isolateStderr_boxed_1097_, v___y_1095_);
return v_res_1098_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = 1;
v___x_1108_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1109_ = l_Lean_Name_toString(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1110_, lean_object* v_cmdState_1111_, lean_object* v_beginPos_1112_, lean_object* v_snap_1113_, lean_object* v_cancelTk_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_env_1117_; lean_object* v_scopes_1118_; lean_object* v_usedQuotCtxts_1119_; lean_object* v_nextMacroScope_1120_; lean_object* v_maxRecDepth_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_infoState_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1200_; 
v_env_1117_ = lean_ctor_get(v_cmdState_1111_, 0);
v_scopes_1118_ = lean_ctor_get(v_cmdState_1111_, 2);
v_usedQuotCtxts_1119_ = lean_ctor_get(v_cmdState_1111_, 3);
v_nextMacroScope_1120_ = lean_ctor_get(v_cmdState_1111_, 4);
v_maxRecDepth_1121_ = lean_ctor_get(v_cmdState_1111_, 5);
v_ngen_1122_ = lean_ctor_get(v_cmdState_1111_, 6);
v_auxDeclNGen_1123_ = lean_ctor_get(v_cmdState_1111_, 7);
v_infoState_1124_ = lean_ctor_get(v_cmdState_1111_, 8);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_cmdState_1111_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; lean_object* v_unused_1202_; lean_object* v_unused_1203_; 
v_unused_1201_ = lean_ctor_get(v_cmdState_1111_, 10);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_cmdState_1111_, 9);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_cmdState_1111_, 1);
lean_dec(v_unused_1203_);
v___x_1126_ = v_cmdState_1111_;
v_isShared_1127_ = v_isSharedCheck_1200_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_infoState_1124_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_maxRecDepth_1121_);
lean_inc(v_nextMacroScope_1120_);
lean_inc(v_usedQuotCtxts_1119_);
lean_inc(v_scopes_1118_);
lean_inc(v_env_1117_);
lean_dec(v_cmdState_1111_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1200_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1128_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1129_ = l_List_head_x21___redArg(v___x_1128_, v_scopes_1118_);
v___x_1130_ = l_Lean_MessageLog_empty;
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1133_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 10, v___x_1133_);
lean_ctor_set(v___x_1126_, 9, v___x_1132_);
lean_ctor_set(v___x_1126_, 1, v___x_1130_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_env_1117_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_scopes_1118_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_usedQuotCtxts_1119_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_nextMacroScope_1120_);
lean_ctor_set(v_reuseFailAlloc_1199_, 5, v_maxRecDepth_1121_);
lean_ctor_set(v_reuseFailAlloc_1199_, 6, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1199_, 7, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1199_, 8, v_infoState_1124_);
lean_ctor_set(v_reuseFailAlloc_1199_, 9, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1199_, 10, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v_toProcessingContext_1137_; lean_object* v_fileName_1138_; lean_object* v_fileMap_1139_; lean_object* v_opts_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; uint8_t v___y_1150_; lean_object* v___y_1151_; lean_object* v_messages_1152_; lean_object* v___y_1178_; 
v___x_1136_ = lean_st_mk_ref(v___x_1135_);
v_toProcessingContext_1137_ = lean_ctor_get(v_a_1115_, 0);
v_fileName_1138_ = lean_ctor_get(v_toProcessingContext_1137_, 1);
lean_inc_ref(v_fileName_1138_);
v_fileMap_1139_ = lean_ctor_get(v_toProcessingContext_1137_, 2);
lean_inc_ref(v_fileMap_1139_);
v_opts_1140_ = lean_ctor_get(v___x_1129_, 1);
lean_inc_ref(v_opts_1140_);
lean_dec(v___x_1129_);
v___f_1141_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1141_, 0, v_stx_1110_);
v___x_1142_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_;
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Lean_firstFrontendMacroScope;
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Lean_internal_cmdlineSnapshots;
v___x_1148_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1140_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1198_; 
lean_inc_ref(v_snap_1113_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_snap_1113_);
v___y_1178_ = v___x_1198_;
goto v___jp_1177_;
}
else
{
v___y_1178_ = v___x_1144_;
goto v___jp_1177_;
}
v___jp_1149_:
{
lean_object* v_new_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v_scopes_1160_; lean_object* v_usedQuotCtxts_1161_; lean_object* v_nextMacroScope_1162_; lean_object* v_maxRecDepth_1163_; lean_object* v_ngen_1164_; lean_object* v_auxDeclNGen_1165_; lean_object* v_infoState_1166_; lean_object* v_traceState_1167_; lean_object* v_snapshotTasks_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_new_1153_ = lean_ctor_get(v_snap_1113_, 1);
lean_inc(v_new_1153_);
lean_dec_ref(v_snap_1113_);
v___x_1154_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1155_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1156_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set(v___x_1156_, 2, v___x_1144_);
lean_ctor_set(v___x_1156_, 3, v___x_1132_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*4, v___y_1150_);
v___x_1157_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1142_, v___x_1156_);
v___x_1158_ = lean_io_promise_resolve(v___x_1157_, v_new_1153_);
lean_dec(v_new_1153_);
v_env_1159_ = lean_ctor_get(v___y_1151_, 0);
v_scopes_1160_ = lean_ctor_get(v___y_1151_, 2);
v_usedQuotCtxts_1161_ = lean_ctor_get(v___y_1151_, 3);
v_nextMacroScope_1162_ = lean_ctor_get(v___y_1151_, 4);
v_maxRecDepth_1163_ = lean_ctor_get(v___y_1151_, 5);
v_ngen_1164_ = lean_ctor_get(v___y_1151_, 6);
v_auxDeclNGen_1165_ = lean_ctor_get(v___y_1151_, 7);
v_infoState_1166_ = lean_ctor_get(v___y_1151_, 8);
v_traceState_1167_ = lean_ctor_get(v___y_1151_, 9);
v_snapshotTasks_1168_ = lean_ctor_get(v___y_1151_, 10);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___y_1151_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___y_1151_, 1);
lean_dec(v_unused_1176_);
v___x_1170_ = v___y_1151_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snapshotTasks_1168_);
lean_inc(v_traceState_1167_);
lean_inc(v_infoState_1166_);
lean_inc(v_auxDeclNGen_1165_);
lean_inc(v_ngen_1164_);
lean_inc(v_maxRecDepth_1163_);
lean_inc(v_nextMacroScope_1162_);
lean_inc(v_usedQuotCtxts_1161_);
lean_inc(v_scopes_1160_);
lean_inc(v_env_1159_);
lean_dec(v___y_1151_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_messages_1152_);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_env_1159_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_messages_1152_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_scopes_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_usedQuotCtxts_1161_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_nextMacroScope_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 5, v_maxRecDepth_1163_);
lean_ctor_set(v_reuseFailAlloc_1174_, 6, v_ngen_1164_);
lean_ctor_set(v_reuseFailAlloc_1174_, 7, v_auxDeclNGen_1165_);
lean_ctor_set(v_reuseFailAlloc_1174_, 8, v_infoState_1166_);
lean_ctor_set(v_reuseFailAlloc_1174_, 9, v_traceState_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 10, v_snapshotTasks_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
v___jp_1177_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v_fst_1186_; lean_object* v___x_1187_; lean_object* v_messages_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_cancelTk_1114_);
v___x_1180_ = 0;
lean_inc(v_beginPos_1112_);
lean_inc_ref(v_fileMap_1139_);
lean_inc_ref(v_fileName_1138_);
v___x_1181_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1181_, 0, v_fileName_1138_);
lean_ctor_set(v___x_1181_, 1, v_fileMap_1139_);
lean_ctor_set(v___x_1181_, 2, v___x_1131_);
lean_ctor_set(v___x_1181_, 3, v_beginPos_1112_);
lean_ctor_set(v___x_1181_, 4, v___x_1143_);
lean_ctor_set(v___x_1181_, 5, v___x_1144_);
lean_ctor_set(v___x_1181_, 6, v___x_1145_);
lean_ctor_set(v___x_1181_, 7, v___x_1146_);
lean_ctor_set(v___x_1181_, 8, v___y_1178_);
lean_ctor_set(v___x_1181_, 9, v___x_1179_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*10, v___x_1180_);
lean_inc(v___x_1136_);
v___f_1182_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1182_, 0, v___f_1141_);
lean_closure_set(v___f_1182_, 1, v___x_1181_);
lean_closure_set(v___f_1182_, 2, v___x_1136_);
v___x_1183_ = l_Lean_Core_stderrAsMessages;
v___x_1184_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1140_, v___x_1183_);
lean_dec_ref(v_opts_1140_);
v___x_1185_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1182_, v___x_1184_, v_a_1115_);
v_fst_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_fst_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = lean_st_ref_get(v___x_1136_);
lean_dec(v___x_1136_);
v_messages_1188_ = lean_ctor_get(v___x_1187_, 1);
lean_inc_ref(v_messages_1188_);
v___x_1189_ = lean_string_utf8_byte_size(v_fst_1186_);
v___x_1190_ = lean_nat_dec_eq(v___x_1189_, v___x_1131_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = l_Lean_FileMap_toPosition(v_fileMap_1139_, v_beginPos_1112_);
lean_dec(v_beginPos_1112_);
v___x_1192_ = 0;
v___x_1193_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_fst_1186_);
v___x_1195_ = l_Lean_MessageData_ofFormat(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1196_, 0, v_fileName_1138_);
lean_ctor_set(v___x_1196_, 1, v___x_1191_);
lean_ctor_set(v___x_1196_, 2, v___x_1144_);
lean_ctor_set(v___x_1196_, 3, v___x_1193_);
lean_ctor_set(v___x_1196_, 4, v___x_1195_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*5, v___x_1180_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*5 + 1, v___x_1192_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*5 + 2, v___x_1180_);
v___x_1197_ = l_Lean_MessageLog_add(v___x_1196_, v_messages_1188_);
v___y_1150_ = v___x_1180_;
v___y_1151_ = v___x_1187_;
v_messages_1152_ = v___x_1197_;
goto v___jp_1149_;
}
else
{
lean_dec(v_fst_1186_);
lean_dec_ref(v_fileMap_1139_);
lean_dec_ref(v_fileName_1138_);
lean_dec(v_beginPos_1112_);
v___y_1150_ = v___x_1180_;
v___y_1151_ = v___x_1187_;
v_messages_1152_ = v_messages_1188_;
goto v___jp_1149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1204_, lean_object* v_cmdState_1205_, lean_object* v_beginPos_1206_, lean_object* v_snap_1207_, lean_object* v_cancelTk_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1204_, v_cmdState_1205_, v_beginPos_1206_, v_snap_1207_, v_cancelTk_1208_, v_a_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1212_, lean_object* v_h_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1213_, v_x_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_h_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1218_, v_h_1219_, v_x_1220_, v___y_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1224_, lean_object* v_x_1225_, uint8_t v_isolateStderr_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1225_, v_isolateStderr_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_x_1231_, lean_object* v_isolateStderr_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_isolateStderr_boxed_1235_; lean_object* v_res_1236_; 
v_isolateStderr_boxed_1235_ = lean_unbox(v_isolateStderr_1232_);
v_res_1236_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1230_, v_x_1231_, v_isolateStderr_boxed_1235_, v___y_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1237_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_opts_1247_, lean_object* v_opt_1248_){
_start:
{
lean_object* v_name_1249_; lean_object* v_defValue_1250_; lean_object* v_map_1251_; lean_object* v___x_1252_; 
v_name_1249_ = lean_ctor_get(v_opt_1248_, 0);
v_defValue_1250_ = lean_ctor_get(v_opt_1248_, 1);
v_map_1251_ = lean_ctor_get(v_opts_1247_, 0);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1251_, v_name_1249_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_inc(v_defValue_1250_);
return v_defValue_1250_;
}
else
{
lean_object* v_val_1253_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref(v___x_1252_);
if (lean_obj_tag(v_val_1253_) == 3)
{
lean_object* v_v_1254_; 
v_v_1254_ = lean_ctor_get(v_val_1253_, 0);
lean_inc(v_v_1254_);
lean_dec_ref(v_val_1253_);
return v_v_1254_;
}
else
{
lean_dec(v_val_1253_);
lean_inc(v_defValue_1250_);
return v_defValue_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0___boxed(lean_object* v_opts_1255_, lean_object* v_opt_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1255_, v_opt_1256_);
lean_dec_ref(v_opt_1256_);
lean_dec_ref(v_opts_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_s_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_s_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_s_1261_){
_start:
{
lean_object* v_toSnapshot_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_toSnapshot_1262_ = lean_ctor_get(v_s_1261_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_s_1261_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v_s_1261_, 1);
lean_dec(v_unused_1271_);
v___x_1264_ = v_s_1261_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_toSnapshot_1262_);
lean_dec(v_s_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_toSnapshot_1262_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_s_1272_){
_start:
{
lean_object* v_tree_1273_; lean_object* v___x_1274_; 
v_tree_1273_ = lean_ctor_get(v_s_1272_, 1);
v___x_1274_ = lean_thunk_get_own(v_tree_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_s_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_s_1275_);
lean_dec_ref(v_s_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v_a_1277_, lean_object* v___x_1278_, lean_object* v_parserState_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v_toProcessingContext_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_toProcessingContext_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc_ref(v_toProcessingContext_1281_);
lean_dec_ref(v_a_1277_);
v___x_1282_ = l_Lean_MessageLog_empty;
v___x_1283_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1281_, v___x_1278_, v_parserState_1279_, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object* v___x_1284_, lean_object* v___x_1285_, lean_object* v___x_1286_, uint8_t v_val_1287_, lean_object* v_as_1288_, size_t v_sz_1289_, size_t v_i_1290_, lean_object* v_b_1291_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_usize_dec_lt(v_i_1290_, v_sz_1289_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v___x_1286_);
lean_dec_ref(v___x_1284_);
return v_b_1291_;
}
else
{
lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1312_; 
v_snd_1294_ = lean_ctor_get(v_b_1291_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_b_1291_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_b_1291_, 0);
lean_dec(v_unused_1313_);
v___x_1296_ = v_b_1291_;
v_isShared_1297_ = v_isSharedCheck_1312_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_dec(v_b_1291_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1312_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_a_1298_; lean_object* v_msg_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_a_1298_ = lean_array_uget_borrowed(v_as_1288_, v_i_1290_);
v_msg_1299_ = lean_ctor_get(v_a_1298_, 1);
v___x_1300_ = lean_box(0);
lean_inc_ref(v___x_1284_);
v___x_1301_ = l_Lean_FileMap_toPosition(v___x_1284_, v___x_1285_);
v___x_1302_ = 0;
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1299_);
lean_inc_ref(v___x_1286_);
v___x_1304_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1304_, 0, v___x_1286_);
lean_ctor_set(v___x_1304_, 1, v___x_1301_);
lean_ctor_set(v___x_1304_, 2, v___x_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1303_);
lean_ctor_set(v___x_1304_, 4, v_msg_1299_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*5, v_val_1287_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*5 + 1, v___x_1302_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*5 + 2, v_val_1287_);
v___x_1305_ = l_Lean_MessageLog_add(v___x_1304_, v_snd_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1305_);
lean_ctor_set(v___x_1296_, 0, v___x_1300_);
v___x_1307_ = v___x_1296_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
size_t v___x_1308_; size_t v___x_1309_; 
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_add(v_i_1290_, v___x_1308_);
v_i_1290_ = v___x_1309_;
v_b_1291_ = v___x_1307_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v_val_1317_, lean_object* v_as_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_val_49017__boxed_1323_; size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_val_49017__boxed_1323_ = lean_unbox(v_val_1317_);
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1314_, v___x_1315_, v___x_1316_, v_val_49017__boxed_1323_, v_as_1318_, v_sz_boxed_1324_, v_i_boxed_1325_, v_b_1321_);
lean_dec_ref(v_as_1318_);
lean_dec(v___x_1315_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, uint8_t v_val_1330_, lean_object* v_as_1331_, size_t v_sz_1332_, size_t v_i_1333_, lean_object* v_b_1334_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1333_, v_sz_1332_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1327_);
return v_b_1334_;
}
else
{
lean_object* v_snd_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1355_; 
v_snd_1337_ = lean_ctor_get(v_b_1334_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_b_1334_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v_b_1334_, 0);
lean_dec(v_unused_1356_);
v___x_1339_ = v_b_1334_;
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_snd_1337_);
lean_dec(v_b_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_a_1341_; lean_object* v_msg_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_a_1341_ = lean_array_uget_borrowed(v_as_1331_, v_i_1333_);
v_msg_1342_ = lean_ctor_get(v_a_1341_, 1);
v___x_1343_ = lean_box(0);
lean_inc_ref(v___x_1327_);
v___x_1344_ = l_Lean_FileMap_toPosition(v___x_1327_, v___x_1328_);
v___x_1345_ = 0;
v___x_1346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1342_);
lean_inc_ref(v___x_1329_);
v___x_1347_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1347_, 0, v___x_1329_);
lean_ctor_set(v___x_1347_, 1, v___x_1344_);
lean_ctor_set(v___x_1347_, 2, v___x_1343_);
lean_ctor_set(v___x_1347_, 3, v___x_1346_);
lean_ctor_set(v___x_1347_, 4, v_msg_1342_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*5, v_val_1330_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*5 + 1, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*5 + 2, v_val_1330_);
v___x_1348_ = l_Lean_MessageLog_add(v___x_1347_, v_snd_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1348_);
lean_ctor_set(v___x_1339_, 0, v___x_1343_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_add(v_i_1333_, v___x_1351_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1327_, v___x_1328_, v___x_1329_, v_val_1330_, v_as_1331_, v_sz_1332_, v___x_1352_, v___x_1350_);
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_val_1360_, lean_object* v_as_1361_, lean_object* v_sz_1362_, lean_object* v_i_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v_val_49069__boxed_1366_; size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_val_49069__boxed_1366_ = lean_unbox(v_val_1360_);
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1362_);
lean_dec(v_sz_1362_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1357_, v___x_1358_, v___x_1359_, v_val_49069__boxed_1366_, v_as_1361_, v_sz_boxed_1367_, v_i_boxed_1368_, v_b_1364_);
lean_dec_ref(v_as_1361_);
lean_dec(v___x_1358_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object* v___x_1370_, lean_object* v___x_1371_, lean_object* v___x_1372_, uint8_t v_val_1373_, lean_object* v_inh_1374_, lean_object* v_n_1375_, lean_object* v_b_1376_){
_start:
{
if (lean_obj_tag(v_n_1375_) == 0)
{
lean_object* v_cs_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1393_; 
v_cs_1378_ = lean_ctor_get(v_n_1375_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_n_1375_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1380_ = v_n_1375_;
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_cs_1378_);
lean_dec(v_n_1375_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; lean_object* v_fst_1387_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_b_1376_);
v_sz_1384_ = lean_array_size(v_cs_1378_);
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v___x_1370_, v___x_1371_, v___x_1372_, v_val_1373_, v_inh_1374_, v_cs_1378_, v_sz_1384_, v___x_1385_, v___x_1383_);
lean_dec_ref(v_cs_1378_);
v_fst_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_fst_1387_);
if (lean_obj_tag(v_fst_1387_) == 0)
{
lean_object* v_snd_1388_; lean_object* v___x_1390_; 
v_snd_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v___x_1386_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 1);
lean_ctor_set(v___x_1380_, 0, v_snd_1388_);
v___x_1390_ = v___x_1380_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_snd_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v_val_1392_; 
lean_dec_ref(v___x_1386_);
lean_del_object(v___x_1380_);
v_val_1392_ = lean_ctor_get(v_fst_1387_, 0);
lean_inc(v_val_1392_);
lean_dec_ref(v_fst_1387_);
return v_val_1392_;
}
}
}
else
{
lean_object* v_vs_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1409_; 
v_vs_1394_ = lean_ctor_get(v_n_1375_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_n_1375_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1396_ = v_n_1375_;
v_isShared_1397_ = v_isSharedCheck_1409_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_vs_1394_);
lean_dec(v_n_1375_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1409_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v_fst_1403_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_b_1376_);
v_sz_1400_ = lean_array_size(v_vs_1394_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1370_, v___x_1371_, v___x_1372_, v_val_1373_, v_vs_1394_, v_sz_1400_, v___x_1401_, v___x_1399_);
lean_dec_ref(v_vs_1394_);
v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_fst_1403_);
if (lean_obj_tag(v_fst_1403_) == 0)
{
lean_object* v_snd_1404_; lean_object* v___x_1406_; 
v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_snd_1404_);
lean_dec_ref(v___x_1402_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v_snd_1404_);
v___x_1406_ = v___x_1396_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_snd_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v_val_1408_; 
lean_dec_ref(v___x_1402_);
lean_del_object(v___x_1396_);
v_val_1408_ = lean_ctor_get(v_fst_1403_, 0);
lean_inc(v_val_1408_);
lean_dec_ref(v_fst_1403_);
return v_val_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, uint8_t v_val_1413_, lean_object* v_inh_1414_, lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1410_);
return v_b_1418_;
}
else
{
lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1439_; 
v_snd_1421_ = lean_ctor_get(v_b_1418_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_b_1418_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_b_1418_, 0);
lean_dec(v_unused_1440_);
v___x_1423_ = v_b_1418_;
v_isShared_1424_ = v_isSharedCheck_1439_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_dec(v_b_1418_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1439_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_array_uget_borrowed(v_as_1415_, v_i_1417_);
lean_inc(v_snd_1421_);
lean_inc(v_a_1425_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1410_);
v___x_1426_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1410_, v___x_1411_, v___x_1412_, v_val_1413_, v_inh_1414_, v_a_1425_, v_snd_1421_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1410_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1421_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec(v_snd_1421_);
v_a_1431_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1426_);
v___x_1432_ = lean_box(0);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_a_1431_);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_a_1431_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
size_t v___x_1435_; size_t v___x_1436_; 
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_i_1417_, v___x_1435_);
v_i_1417_ = v___x_1436_;
v_b_1418_ = v___x_1434_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_val_1444_, lean_object* v_inh_1445_, lean_object* v_as_1446_, lean_object* v_sz_1447_, lean_object* v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_val_49120__boxed_1451_; size_t v_sz_boxed_1452_; size_t v_i_boxed_1453_; lean_object* v_res_1454_; 
v_val_49120__boxed_1451_ = lean_unbox(v_val_1444_);
v_sz_boxed_1452_ = lean_unbox_usize(v_sz_1447_);
lean_dec(v_sz_1447_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v___x_1441_, v___x_1442_, v___x_1443_, v_val_49120__boxed_1451_, v_inh_1445_, v_as_1446_, v_sz_boxed_1452_, v_i_boxed_1453_, v_b_1449_);
lean_dec_ref(v_as_1446_);
lean_dec_ref(v_inh_1445_);
lean_dec(v___x_1442_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, lean_object* v_val_1458_, lean_object* v_inh_1459_, lean_object* v_n_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_val_49136__boxed_1463_; lean_object* v_res_1464_; 
v_val_49136__boxed_1463_ = lean_unbox(v_val_1458_);
v_res_1464_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1455_, v___x_1456_, v___x_1457_, v_val_49136__boxed_1463_, v_inh_1459_, v_n_1460_, v_b_1461_);
lean_dec_ref(v_inh_1459_);
lean_dec(v___x_1456_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1465_, lean_object* v___x_1466_, lean_object* v___x_1467_, uint8_t v_val_1468_, lean_object* v_as_1469_, size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_b_1472_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___x_1465_);
return v_b_1472_;
}
else
{
lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1493_; 
v_snd_1475_ = lean_ctor_get(v_b_1472_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_b_1472_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_b_1472_, 0);
lean_dec(v_unused_1494_);
v___x_1477_ = v_b_1472_;
v_isShared_1478_ = v_isSharedCheck_1493_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_dec(v_b_1472_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1493_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_a_1479_; lean_object* v_msg_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v_a_1479_ = lean_array_uget_borrowed(v_as_1469_, v_i_1471_);
v_msg_1480_ = lean_ctor_get(v_a_1479_, 1);
v___x_1481_ = lean_box(0);
lean_inc_ref(v___x_1465_);
v___x_1482_ = l_Lean_FileMap_toPosition(v___x_1465_, v___x_1466_);
v___x_1483_ = 0;
v___x_1484_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1480_);
lean_inc_ref(v___x_1467_);
v___x_1485_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1485_, 0, v___x_1467_);
lean_ctor_set(v___x_1485_, 1, v___x_1482_);
lean_ctor_set(v___x_1485_, 2, v___x_1481_);
lean_ctor_set(v___x_1485_, 3, v___x_1484_);
lean_ctor_set(v___x_1485_, 4, v_msg_1480_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*5, v_val_1468_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*5 + 1, v___x_1483_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*5 + 2, v_val_1468_);
v___x_1486_ = l_Lean_MessageLog_add(v___x_1485_, v_snd_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1486_);
lean_ctor_set(v___x_1477_, 0, v___x_1481_);
v___x_1488_ = v___x_1477_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
size_t v___x_1489_; size_t v___x_1490_; 
v___x_1489_ = ((size_t)1ULL);
v___x_1490_ = lean_usize_add(v_i_1471_, v___x_1489_);
v_i_1471_ = v___x_1490_;
v_b_1472_ = v___x_1488_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1495_, lean_object* v___x_1496_, lean_object* v___x_1497_, lean_object* v_val_1498_, lean_object* v_as_1499_, lean_object* v_sz_1500_, lean_object* v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_val_49242__boxed_1504_; size_t v_sz_boxed_1505_; size_t v_i_boxed_1506_; lean_object* v_res_1507_; 
v_val_49242__boxed_1504_ = lean_unbox(v_val_1498_);
v_sz_boxed_1505_ = lean_unbox_usize(v_sz_1500_);
lean_dec(v_sz_1500_);
v_i_boxed_1506_ = lean_unbox_usize(v_i_1501_);
lean_dec(v_i_1501_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1495_, v___x_1496_, v___x_1497_, v_val_49242__boxed_1504_, v_as_1499_, v_sz_boxed_1505_, v_i_boxed_1506_, v_b_1502_);
lean_dec_ref(v_as_1499_);
lean_dec(v___x_1496_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1508_, lean_object* v___x_1509_, lean_object* v___x_1510_, uint8_t v_val_1511_, lean_object* v_as_1512_, size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_b_1515_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_lt(v_i_1514_, v_sz_1513_);
if (v___x_1517_ == 0)
{
lean_dec_ref(v___x_1510_);
lean_dec_ref(v___x_1508_);
return v_b_1515_;
}
else
{
lean_object* v_snd_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1536_; 
v_snd_1518_ = lean_ctor_get(v_b_1515_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_b_1515_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_b_1515_, 0);
lean_dec(v_unused_1537_);
v___x_1520_ = v_b_1515_;
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snd_1518_);
lean_dec(v_b_1515_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_a_1522_; lean_object* v_msg_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v_a_1522_ = lean_array_uget_borrowed(v_as_1512_, v_i_1514_);
v_msg_1523_ = lean_ctor_get(v_a_1522_, 1);
v___x_1524_ = lean_box(0);
lean_inc_ref(v___x_1508_);
v___x_1525_ = l_Lean_FileMap_toPosition(v___x_1508_, v___x_1509_);
v___x_1526_ = 0;
v___x_1527_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1523_);
lean_inc_ref(v___x_1510_);
v___x_1528_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1528_, 0, v___x_1510_);
lean_ctor_set(v___x_1528_, 1, v___x_1525_);
lean_ctor_set(v___x_1528_, 2, v___x_1524_);
lean_ctor_set(v___x_1528_, 3, v___x_1527_);
lean_ctor_set(v___x_1528_, 4, v_msg_1523_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*5, v_val_1511_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*5 + 1, v___x_1526_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*5 + 2, v_val_1511_);
v___x_1529_ = l_Lean_MessageLog_add(v___x_1528_, v_snd_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v___x_1529_);
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((size_t)1ULL);
v___x_1533_ = lean_usize_add(v_i_1514_, v___x_1532_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1508_, v___x_1509_, v___x_1510_, v_val_1511_, v_as_1512_, v_sz_1513_, v___x_1533_, v___x_1531_);
return v___x_1534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v_val_1541_, lean_object* v_as_1542_, lean_object* v_sz_1543_, lean_object* v_i_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_val_49294__boxed_1547_; size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_val_49294__boxed_1547_ = lean_unbox(v_val_1541_);
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1543_);
lean_dec(v_sz_1543_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1538_, v___x_1539_, v___x_1540_, v_val_49294__boxed_1547_, v_as_1542_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1545_);
lean_dec_ref(v_as_1542_);
lean_dec(v___x_1539_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1551_, lean_object* v___x_1552_, lean_object* v___x_1553_, uint8_t v_val_1554_, lean_object* v_t_1555_, lean_object* v_init_1556_){
_start:
{
lean_object* v_root_1558_; lean_object* v_tail_1559_; lean_object* v___x_1560_; 
v_root_1558_ = lean_ctor_get(v_t_1555_, 0);
lean_inc_ref(v_root_1558_);
v_tail_1559_ = lean_ctor_get(v_t_1555_, 1);
lean_inc_ref(v_tail_1559_);
lean_dec_ref(v_t_1555_);
lean_inc_ref(v_init_1556_);
lean_inc_ref(v___x_1553_);
lean_inc_ref(v___x_1551_);
v___x_1560_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1551_, v___x_1552_, v___x_1553_, v_val_1554_, v_init_1556_, v_root_1558_, v_init_1556_);
lean_dec_ref(v_init_1556_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
lean_dec_ref(v_tail_1559_);
lean_dec_ref(v___x_1553_);
lean_dec_ref(v___x_1551_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
return v_a_1561_;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v_fst_1568_; 
v_a_1562_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1560_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1562_);
v_sz_1565_ = lean_array_size(v_tail_1559_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1551_, v___x_1552_, v___x_1553_, v_val_1554_, v_tail_1559_, v_sz_1565_, v___x_1566_, v___x_1564_);
lean_dec_ref(v_tail_1559_);
v_fst_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_fst_1568_);
if (lean_obj_tag(v_fst_1568_) == 0)
{
lean_object* v_snd_1569_; 
v_snd_1569_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_snd_1569_);
lean_dec_ref(v___x_1567_);
return v_snd_1569_;
}
else
{
lean_object* v_val_1570_; 
lean_dec_ref(v___x_1567_);
v_val_1570_ = lean_ctor_get(v_fst_1568_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v_fst_1568_);
return v_val_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_val_1574_, lean_object* v_t_1575_, lean_object* v_init_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v_val_49345__boxed_1578_; lean_object* v_res_1579_; 
v_val_49345__boxed_1578_ = lean_unbox(v_val_1574_);
v_res_1579_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1571_, v___x_1572_, v___x_1573_, v_val_49345__boxed_1578_, v_t_1575_, v_init_1576_);
lean_dec(v___x_1572_);
return v_res_1579_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = l_Lean_firstFrontendMacroScope;
v___x_1582_ = lean_nat_add(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1589_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, size_t v___x_1597_, uint8_t v___x_1598_, lean_object* v_env_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_a_1602_, lean_object* v_opts_1603_, lean_object* v___x_1604_, lean_object* v_pos_1605_, uint8_t v_val_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, uint8_t v___x_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_toProcessingContext_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1700_; 
v___x_1614_ = l_Lean_firstFrontendMacroScope;
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1617_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1618_ = lean_box(0);
lean_inc(v___x_1594_);
v___x_1619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1594_);
lean_ctor_set(v___x_1619_, 1, v___x_1615_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
v___x_1620_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1621_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1622_ = lean_mk_empty_array_with_capacity(v___x_1595_);
lean_inc_ref(v___x_1622_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_inc_n(v___x_1596_, 2);
v___x_1624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1622_);
lean_ctor_set(v___x_1624_, 2, v___x_1596_);
lean_ctor_set(v___x_1624_, 3, v___x_1596_);
lean_ctor_set_usize(v___x_1624_, 4, v___x_1597_);
v___x_1625_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1624_, 2);
v___x_1626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1624_);
lean_ctor_set(v___x_1626_, 2, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1627_, 0, v___x_1620_);
lean_ctor_set(v___x_1627_, 1, v___x_1620_);
lean_ctor_set(v___x_1627_, 2, v___x_1624_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*3, v___x_1598_);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1596_);
lean_inc_ref(v___x_1628_);
lean_inc_ref(v___x_1600_);
v___x_1629_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1629_, 0, v_env_1599_);
lean_ctor_set(v___x_1629_, 1, v___x_1616_);
lean_ctor_set(v___x_1629_, 2, v___x_1617_);
lean_ctor_set(v___x_1629_, 3, v___x_1619_);
lean_ctor_set(v___x_1629_, 4, v___x_1600_);
lean_ctor_set(v___x_1629_, 5, v___x_1621_);
lean_ctor_set(v___x_1629_, 6, v___x_1626_);
lean_ctor_set(v___x_1629_, 7, v___x_1627_);
lean_ctor_set(v___x_1629_, 8, v___x_1628_);
v___x_1630_ = lean_st_mk_ref(v___x_1629_);
v___x_1631_ = lean_st_ref_get(v___x_1601_);
v___x_1632_ = lean_st_ref_get(v___x_1630_);
v_toProcessingContext_1633_ = lean_ctor_get(v_a_1602_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_a_1602_, 1);
lean_dec(v_unused_1701_);
v___x_1635_ = v_a_1602_;
v_isShared_1636_ = v_isSharedCheck_1700_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_toProcessingContext_1633_);
lean_dec(v_a_1602_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1700_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_fileName_1637_; lean_object* v_fileMap_1638_; lean_object* v_env_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v_fileName_1645_; lean_object* v_fileMap_1646_; lean_object* v_currRecDepth_1647_; lean_object* v_ref_1648_; lean_object* v_currNamespace_1649_; lean_object* v_openDecls_1650_; lean_object* v_initHeartbeats_1651_; lean_object* v_maxHeartbeats_1652_; lean_object* v_quotContext_1653_; lean_object* v_currMacroScope_1654_; lean_object* v_cancelTk_x3f_1655_; uint8_t v_suppressElabErrors_1656_; lean_object* v_inheritedTraceOptions_1657_; lean_object* v___y_1658_; uint8_t v___y_1679_; uint8_t v___x_1699_; 
v_fileName_1637_ = lean_ctor_get(v_toProcessingContext_1633_, 1);
lean_inc_ref(v_fileName_1637_);
v_fileMap_1638_ = lean_ctor_get(v_toProcessingContext_1633_, 2);
lean_inc_ref(v_fileMap_1638_);
lean_dec_ref(v_toProcessingContext_1633_);
v_env_1639_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1632_);
v___x_1640_ = lean_box(0);
v___x_1641_ = l_Lean_Core_getMaxHeartbeats(v_opts_1603_);
v___x_1642_ = l_Lean_diagnostics;
v___x_1643_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1603_, v___x_1642_);
v___x_1699_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1639_);
lean_dec_ref(v_env_1639_);
if (v___x_1699_ == 0)
{
if (v___x_1643_ == 0)
{
v___y_1679_ = v___x_1611_;
goto v___jp_1678_;
}
else
{
v___y_1679_ = v___x_1699_;
goto v___jp_1678_;
}
}
else
{
v___y_1679_ = v___x_1643_;
goto v___jp_1678_;
}
v___jp_1644_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = l_Lean_maxRecDepth;
v___x_1660_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1603_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1661_, 0, v_fileName_1645_);
lean_ctor_set(v___x_1661_, 1, v_fileMap_1646_);
lean_ctor_set(v___x_1661_, 2, v_opts_1603_);
lean_ctor_set(v___x_1661_, 3, v_currRecDepth_1647_);
lean_ctor_set(v___x_1661_, 4, v___x_1660_);
lean_ctor_set(v___x_1661_, 5, v_ref_1648_);
lean_ctor_set(v___x_1661_, 6, v_currNamespace_1649_);
lean_ctor_set(v___x_1661_, 7, v_openDecls_1650_);
lean_ctor_set(v___x_1661_, 8, v_initHeartbeats_1651_);
lean_ctor_set(v___x_1661_, 9, v_maxHeartbeats_1652_);
lean_ctor_set(v___x_1661_, 10, v_quotContext_1653_);
lean_ctor_set(v___x_1661_, 11, v_currMacroScope_1654_);
lean_ctor_set(v___x_1661_, 12, v_cancelTk_x3f_1655_);
lean_ctor_set(v___x_1661_, 13, v_inheritedTraceOptions_1657_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*14, v___x_1643_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*14 + 1, v_suppressElabErrors_1656_);
v___x_1662_ = l_Lean_Language_SnapshotTree_trace(v___x_1604_, v___x_1661_, v___y_1658_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; lean_object* v_traceState_1664_; lean_object* v_traces_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_dec_ref(v___x_1662_);
lean_dec_ref(v___x_1609_);
v___x_1663_ = lean_st_ref_get(v___x_1630_);
lean_dec(v___x_1630_);
v_traceState_1664_ = lean_ctor_get(v___x_1663_, 4);
lean_inc_ref(v_traceState_1664_);
lean_dec(v___x_1663_);
v_traces_1665_ = lean_ctor_get(v_traceState_1664_, 0);
lean_inc_ref(v_traces_1665_);
lean_dec_ref(v_traceState_1664_);
v___x_1666_ = l_Lean_MessageLog_empty;
v___x_1667_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1638_, v_pos_1605_, v_fileName_1637_, v_val_1606_, v_traces_1665_, v___x_1666_);
v___x_1668_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1607_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
lean_ctor_set(v___x_1669_, 2, v___x_1608_);
lean_ctor_set(v___x_1669_, 3, v___x_1600_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*4, v_val_1606_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___x_1628_);
lean_ctor_set(v___x_1635_, 0, v___x_1669_);
v___x_1671_ = v___x_1635_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1628_);
v___x_1671_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_task_pure(v___x_1671_);
return v___x_1672_;
}
}
else
{
lean_object* v___x_1675_; 
lean_dec_ref(v___x_1662_);
lean_dec_ref(v_fileMap_1638_);
lean_dec_ref(v_fileName_1637_);
lean_dec(v___x_1630_);
lean_dec(v___x_1608_);
lean_dec_ref(v___x_1607_);
lean_dec_ref(v___x_1600_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___x_1628_);
lean_ctor_set(v___x_1635_, 0, v___x_1609_);
v___x_1675_ = v___x_1635_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1628_);
v___x_1675_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_task_pure(v___x_1675_);
return v___x_1676_;
}
}
}
v___jp_1678_:
{
if (v___y_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v_env_1681_; lean_object* v_nextMacroScope_1682_; lean_object* v_ngen_1683_; lean_object* v_auxDeclNGen_1684_; lean_object* v_traceState_1685_; lean_object* v_messages_1686_; lean_object* v_infoState_1687_; lean_object* v_snapshotTasks_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1697_; 
v___x_1680_ = lean_st_ref_take(v___x_1630_);
v_env_1681_ = lean_ctor_get(v___x_1680_, 0);
v_nextMacroScope_1682_ = lean_ctor_get(v___x_1680_, 1);
v_ngen_1683_ = lean_ctor_get(v___x_1680_, 2);
v_auxDeclNGen_1684_ = lean_ctor_get(v___x_1680_, 3);
v_traceState_1685_ = lean_ctor_get(v___x_1680_, 4);
v_messages_1686_ = lean_ctor_get(v___x_1680_, 6);
v_infoState_1687_ = lean_ctor_get(v___x_1680_, 7);
v_snapshotTasks_1688_ = lean_ctor_get(v___x_1680_, 8);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v___x_1680_, 5);
lean_dec(v_unused_1698_);
v___x_1690_ = v___x_1680_;
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snapshotTasks_1688_);
lean_inc(v_infoState_1687_);
lean_inc(v_messages_1686_);
lean_inc(v_traceState_1685_);
lean_inc(v_auxDeclNGen_1684_);
lean_inc(v_ngen_1683_);
lean_inc(v_nextMacroScope_1682_);
lean_inc(v_env_1681_);
lean_dec(v___x_1680_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = l_Lean_Kernel_enableDiag(v_env_1681_, v___x_1643_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 5, v___x_1621_);
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_nextMacroScope_1682_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_ngen_1683_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_auxDeclNGen_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_traceState_1685_);
lean_ctor_set(v_reuseFailAlloc_1696_, 5, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1696_, 6, v_messages_1686_);
lean_ctor_set(v_reuseFailAlloc_1696_, 7, v_infoState_1687_);
lean_ctor_set(v_reuseFailAlloc_1696_, 8, v_snapshotTasks_1688_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_st_ref_set(v___x_1630_, v___x_1694_);
lean_inc(v___x_1630_);
lean_inc(v___x_1594_);
lean_inc(v___x_1596_);
lean_inc_ref(v_fileMap_1638_);
lean_inc_ref(v_fileName_1637_);
v_fileName_1645_ = v_fileName_1637_;
v_fileMap_1646_ = v_fileMap_1638_;
v_currRecDepth_1647_ = v___x_1596_;
v_ref_1648_ = v___x_1640_;
v_currNamespace_1649_ = v___x_1594_;
v_openDecls_1650_ = v___x_1618_;
v_initHeartbeats_1651_ = v___x_1596_;
v_maxHeartbeats_1652_ = v___x_1641_;
v_quotContext_1653_ = v___x_1594_;
v_currMacroScope_1654_ = v___x_1614_;
v_cancelTk_x3f_1655_ = v___x_1610_;
v_suppressElabErrors_1656_ = v_val_1606_;
v_inheritedTraceOptions_1657_ = v___x_1631_;
v___y_1658_ = v___x_1630_;
goto v___jp_1644_;
}
}
}
else
{
lean_inc(v___x_1630_);
lean_inc(v___x_1594_);
lean_inc(v___x_1596_);
lean_inc_ref(v_fileMap_1638_);
lean_inc_ref(v_fileName_1637_);
v_fileName_1645_ = v_fileName_1637_;
v_fileMap_1646_ = v_fileMap_1638_;
v_currRecDepth_1647_ = v___x_1596_;
v_ref_1648_ = v___x_1640_;
v_currNamespace_1649_ = v___x_1594_;
v_openDecls_1650_ = v___x_1618_;
v_initHeartbeats_1651_ = v___x_1596_;
v_maxHeartbeats_1652_ = v___x_1641_;
v_quotContext_1653_ = v___x_1594_;
v_currMacroScope_1654_ = v___x_1614_;
v_cancelTk_x3f_1655_ = v___x_1610_;
v_suppressElabErrors_1656_ = v_val_1606_;
v_inheritedTraceOptions_1657_ = v___x_1631_;
v___y_1658_ = v___x_1630_;
goto v___jp_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1702_ = _args[0];
lean_object* v___x_1703_ = _args[1];
lean_object* v___x_1704_ = _args[2];
lean_object* v___x_1705_ = _args[3];
lean_object* v___x_1706_ = _args[4];
lean_object* v_env_1707_ = _args[5];
lean_object* v___x_1708_ = _args[6];
lean_object* v___x_1709_ = _args[7];
lean_object* v_a_1710_ = _args[8];
lean_object* v_opts_1711_ = _args[9];
lean_object* v___x_1712_ = _args[10];
lean_object* v_pos_1713_ = _args[11];
lean_object* v_val_1714_ = _args[12];
lean_object* v___x_1715_ = _args[13];
lean_object* v___x_1716_ = _args[14];
lean_object* v___x_1717_ = _args[15];
lean_object* v___x_1718_ = _args[16];
lean_object* v___x_1719_ = _args[17];
lean_object* v_x_1720_ = _args[18];
lean_object* v___y_1721_ = _args[19];
_start:
{
size_t v___x_49406__boxed_1722_; uint8_t v___x_49407__boxed_1723_; uint8_t v_val_49412__boxed_1724_; uint8_t v___x_49417__boxed_1725_; lean_object* v_res_1726_; 
v___x_49406__boxed_1722_ = lean_unbox_usize(v___x_1705_);
lean_dec(v___x_1705_);
v___x_49407__boxed_1723_ = lean_unbox(v___x_1706_);
v_val_49412__boxed_1724_ = lean_unbox(v_val_1714_);
v___x_49417__boxed_1725_ = lean_unbox(v___x_1719_);
v_res_1726_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1702_, v___x_1703_, v___x_1704_, v___x_49406__boxed_1722_, v___x_49407__boxed_1723_, v_env_1707_, v___x_1708_, v___x_1709_, v_a_1710_, v_opts_1711_, v___x_1712_, v_pos_1713_, v_val_49412__boxed_1724_, v___x_1715_, v___x_1716_, v___x_1717_, v___x_1718_, v___x_49417__boxed_1725_, v_x_1720_);
lean_dec(v_pos_1713_);
lean_dec(v___x_1709_);
lean_dec(v___x_1703_);
return v_res_1726_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1733_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1734_ = l_Lean_Name_append(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1735_, lean_object* v___x_1736_, uint8_t v_val_1737_, lean_object* v_val_1738_, lean_object* v_val_1739_, lean_object* v___x_1740_, lean_object* v___x_1741_, uint8_t v___x_1742_, lean_object* v_a_1743_, lean_object* v_pos_1744_, lean_object* v_infoSt_1745_){
_start:
{
lean_object* v___y_1748_; lean_object* v_msgLog_1749_; lean_object* v___y_1755_; lean_object* v_trees_1794_; lean_object* v_size_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_trees_1794_ = lean_ctor_get(v_infoSt_1745_, 2);
lean_inc_ref(v_trees_1794_);
lean_dec_ref(v_infoSt_1745_);
v_size_1795_ = lean_ctor_get(v_trees_1794_, 2);
v___x_1796_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1797_ = lean_nat_dec_lt(v___x_1741_, v_size_1795_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v_trees_1794_);
v___x_1798_ = l_outOfBounds___redArg(v___x_1796_);
v___y_1755_ = v___x_1798_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1796_, v_trees_1794_, v___x_1741_);
v___y_1755_ = v___x_1799_;
goto v___jp_1754_;
}
v___jp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1749_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1748_);
v___x_1752_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1752_, 0, v___x_1735_);
lean_ctor_set(v___x_1752_, 1, v___x_1750_);
lean_ctor_set(v___x_1752_, 2, v___x_1751_);
lean_ctor_set(v___x_1752_, 3, v___x_1736_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*4, v_val_1737_);
v___x_1753_ = lean_io_promise_resolve(v___x_1752_, v_val_1738_);
return v___x_1753_;
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_scopes_1758_; lean_object* v___x_1759_; lean_object* v_opts_1760_; uint8_t v_hasTrace_1761_; lean_object* v___x_1762_; 
v___x_1756_ = l_Lean_inheritedTraceOptions;
v___x_1757_ = lean_st_ref_get(v___x_1756_);
v_scopes_1758_ = lean_ctor_get(v_val_1739_, 2);
v___x_1759_ = l_List_head_x21___redArg(v___x_1740_, v_scopes_1758_);
v_opts_1760_ = lean_ctor_get(v___x_1759_, 1);
lean_inc_ref(v_opts_1760_);
lean_dec(v___x_1759_);
v_hasTrace_1761_ = lean_ctor_get_uint8(v_opts_1760_, sizeof(void*)*1);
v___x_1762_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1761_ == 0)
{
lean_dec_ref(v_opts_1760_);
lean_dec(v___x_1757_);
lean_dec_ref(v_a_1743_);
lean_dec(v___x_1741_);
v___y_1748_ = v___y_1755_;
v_msgLog_1749_ = v___x_1762_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1764_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1765_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1757_, v_opts_1760_, v___x_1765_);
lean_dec_ref(v_opts_1760_);
lean_dec(v___x_1757_);
if (v___x_1766_ == 0)
{
lean_dec_ref(v_a_1743_);
lean_dec(v___x_1741_);
v___y_1748_ = v___y_1755_;
v_msgLog_1749_ = v___x_1762_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_box(0);
lean_inc_ref(v___y_1755_);
v___x_1768_ = l_Lean_Elab_InfoTree_format(v___y_1755_, v___x_1767_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; double v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_toProcessingContext_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1792_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = lean_float_of_nat(v___x_1741_);
v___x_1771_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1772_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1772_, 0, v___x_1763_);
lean_ctor_set(v___x_1772_, 1, v___x_1767_);
lean_ctor_set(v___x_1772_, 2, v___x_1771_);
lean_ctor_set_float(v___x_1772_, sizeof(void*)*3, v___x_1770_);
lean_ctor_set_float(v___x_1772_, sizeof(void*)*3 + 8, v___x_1770_);
lean_ctor_set_uint8(v___x_1772_, sizeof(void*)*3 + 16, v___x_1742_);
v_toProcessingContext_1773_ = lean_ctor_get(v_a_1743_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_a_1743_, 1);
lean_dec(v_unused_1793_);
v___x_1775_ = v_a_1743_;
v_isShared_1776_ = v_isSharedCheck_1792_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_toProcessingContext_1773_);
lean_dec(v_a_1743_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1792_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_fileName_1777_; lean_object* v_fileMap_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v_fileName_1777_ = lean_ctor_get(v_toProcessingContext_1773_, 1);
lean_inc_ref(v_fileName_1777_);
v_fileMap_1778_ = lean_ctor_get(v_toProcessingContext_1773_, 2);
lean_inc_ref(v_fileMap_1778_);
lean_dec_ref(v_toProcessingContext_1773_);
v___x_1779_ = l_Lean_MessageData_nil;
v___x_1780_ = l_Lean_MessageData_ofFormat(v_a_1769_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_mk_empty_array_with_capacity(v___x_1781_);
v___x_1783_ = lean_array_push(v___x_1782_, v___x_1780_);
v___x_1784_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1772_);
lean_ctor_set(v___x_1784_, 1, v___x_1779_);
lean_ctor_set(v___x_1784_, 2, v___x_1783_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 8);
lean_ctor_set(v___x_1775_, 1, v___x_1784_);
lean_ctor_set(v___x_1775_, 0, v___x_1764_);
v___x_1786_ = v___x_1775_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = l_Lean_FileMap_toPosition(v_fileMap_1778_, v_pos_1744_);
v___x_1788_ = 0;
v___x_1789_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1789_, 0, v_fileName_1777_);
lean_ctor_set(v___x_1789_, 1, v___x_1787_);
lean_ctor_set(v___x_1789_, 2, v___x_1767_);
lean_ctor_set(v___x_1789_, 3, v___x_1771_);
lean_ctor_set(v___x_1789_, 4, v___x_1786_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*5, v_val_1737_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*5 + 1, v___x_1788_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*5 + 2, v_val_1737_);
v___x_1790_ = l_Lean_MessageLog_add(v___x_1789_, v___x_1762_);
v___y_1748_ = v___y_1755_;
v_msgLog_1749_ = v___x_1790_;
goto v___jp_1747_;
}
}
}
else
{
lean_dec_ref(v___x_1768_);
lean_dec_ref(v_a_1743_);
lean_dec(v___x_1741_);
v___y_1748_ = v___y_1755_;
v_msgLog_1749_ = v___x_1762_;
goto v___jp_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1800_, lean_object* v___x_1801_, lean_object* v_val_1802_, lean_object* v_val_1803_, lean_object* v_val_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_a_1808_, lean_object* v_pos_1809_, lean_object* v_infoSt_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_val_49614__boxed_1812_; uint8_t v___x_49619__boxed_1813_; lean_object* v_res_1814_; 
v_val_49614__boxed_1812_ = lean_unbox(v_val_1802_);
v___x_49619__boxed_1813_ = lean_unbox(v___x_1807_);
v_res_1814_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1800_, v___x_1801_, v_val_49614__boxed_1812_, v_val_1803_, v_val_1804_, v___x_1805_, v___x_1806_, v___x_49619__boxed_1813_, v_a_1808_, v_pos_1809_, v_infoSt_1810_);
lean_dec(v_pos_1809_);
lean_dec_ref(v_val_1804_);
lean_dec(v_val_1803_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1816_, size_t v_i_1817_, size_t v_stop_1818_, lean_object* v_b_1819_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_eq(v_i_1817_, v_stop_1818_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___f_1823_; lean_object* v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; 
v___x_1822_ = lean_array_uget_borrowed(v_as_1816_, v_i_1817_);
v___f_1823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1822_);
v___x_1824_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1823_, v___x_1822_);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1817_, v___x_1825_);
v_i_1817_ = v___x_1826_;
v_b_1819_ = v___x_1824_;
goto _start;
}
else
{
return v_b_1819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_){
_start:
{
size_t v_i_boxed_1833_; size_t v_stop_boxed_1834_; lean_object* v_res_1835_; 
v_i_boxed_1833_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1834_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1828_, v_i_boxed_1833_, v_stop_boxed_1834_, v_b_1831_);
lean_dec_ref(v_as_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1836_, lean_object* v_newParserState_1837_, lean_object* v_val_1838_, lean_object* v_sync_1839_, lean_object* v_val_1840_, lean_object* v_a_1841_, lean_object* v_oldNext_1842_, lean_object* v___y_1843_){
_start:
{
uint8_t v_sync_boxed_1844_; lean_object* v_res_1845_; 
v_sync_boxed_1844_ = lean_unbox(v_sync_1839_);
v_res_1845_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1836_, v_newParserState_1837_, v_val_1838_, v_sync_boxed_1844_, v_val_1840_, v_a_1841_, v_oldNext_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1846_, lean_object* v_newParserState_1847_, lean_object* v_val_1848_, uint8_t v_sync_1849_, lean_object* v_val_1850_, lean_object* v_a_1851_, lean_object* v_oldResult_1852_){
_start:
{
lean_object* v_task_1854_; lean_object* v___x_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v_task_1854_ = lean_ctor_get(v_val_1846_, 3);
lean_inc_ref(v_task_1854_);
lean_dec_ref(v_val_1846_);
v___x_1855_ = lean_box(v_sync_1849_);
v___f_1856_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1856_, 0, v_oldResult_1852_);
lean_closure_set(v___f_1856_, 1, v_newParserState_1847_);
lean_closure_set(v___f_1856_, 2, v_val_1848_);
lean_closure_set(v___f_1856_, 3, v___x_1855_);
lean_closure_set(v___f_1856_, 4, v_val_1850_);
lean_closure_set(v___f_1856_, 5, v_a_1851_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = 1;
v___x_1859_ = l_BaseIO_chainTask___redArg(v_task_1854_, v___f_1856_, v___x_1857_, v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1860_, lean_object* v_newParserState_1861_, lean_object* v_val_1862_, lean_object* v_sync_1863_, lean_object* v_val_1864_, lean_object* v_a_1865_, lean_object* v_oldResult_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_sync_boxed_1868_; lean_object* v_res_1869_; 
v_sync_boxed_1868_ = lean_unbox(v_sync_1863_);
v_res_1869_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1860_, v_newParserState_1861_, v_val_1862_, v_sync_boxed_1868_, v_val_1864_, v_a_1865_, v_oldResult_1866_);
return v_res_1869_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1872_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1874_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1883_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1884_ = l_Lean_Name_append(v___x_1883_, v___x_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1885_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1888_, lean_object* v_val_1889_, lean_object* v_fst_1890_, uint8_t v_val_1891_, lean_object* v_a_1892_, lean_object* v_snd_1893_, lean_object* v___x_1894_, uint8_t v___x_1895_, lean_object* v_fst_1896_, lean_object* v_val_1897_, lean_object* v_val_1898_, lean_object* v_val_1899_, lean_object* v_snd_1900_, lean_object* v_prom_1901_, lean_object* v___x_1902_, lean_object* v___f_1903_, lean_object* v___f_1904_, lean_object* v___f_1905_, lean_object* v_pos_1906_, lean_object* v_fst_1907_, lean_object* v_cmdState_1908_, lean_object* v_opts_1909_, lean_object* v___x_1910_, lean_object* v_old_x3f_1911_, lean_object* v_parseCancelTk_1912_, lean_object* v_next_x3f_1913_){
_start:
{
lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_snapshotTasks_1920_; lean_object* v___y_1921_; lean_object* v_traceTask_1922_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; size_t v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v_env_1957_; lean_object* v_messages_1958_; lean_object* v_scopes_1959_; lean_object* v_infoState_1960_; lean_object* v_traceState_1961_; lean_object* v_snapshotTasks_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v_reportedCmdState_1971_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; size_t v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v_reportedCmdState_2028_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; size_t v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; size_t v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2091_; 
if (lean_obj_tag(v_next_x3f_1913_) == 0)
{
lean_object* v___x_2144_; 
lean_dec(v_parseCancelTk_1912_);
v___x_2144_ = lean_box(0);
v___y_2091_ = v___x_2144_;
goto v___jp_2090_;
}
else
{
lean_object* v_toProcessingContext_2145_; lean_object* v_val_2146_; lean_object* v_pos_2147_; lean_object* v_endPos_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2161_; 
v_toProcessingContext_2145_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_toProcessingContext_2145_);
v_val_2146_ = lean_ctor_get(v_next_x3f_1913_, 0);
v_pos_2147_ = lean_ctor_get(v_fst_1890_, 0);
v_endPos_2148_ = lean_ctor_get(v_toProcessingContext_2145_, 3);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toProcessingContext_2145_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; 
v_unused_2162_ = lean_ctor_get(v_toProcessingContext_2145_, 2);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_toProcessingContext_2145_, 1);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_toProcessingContext_2145_, 0);
lean_dec(v_unused_2164_);
v___x_2150_ = v_toProcessingContext_2145_;
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_endPos_2148_);
lean_dec(v_toProcessingContext_2145_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2152_ = lean_box(0);
lean_inc(v_pos_2147_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_pos_2147_);
lean_ctor_set(v___x_2153_, 1, v_endPos_2148_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_parseCancelTk_1912_);
v___x_2156_ = l_IO_Promise_result_x21___redArg(v_val_2146_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 3, v___x_2156_);
lean_ctor_set(v___x_2150_, 2, v___x_2155_);
lean_ctor_set(v___x_2150_, 1, v___x_2154_);
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2158_ = v___x_2150_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
v___y_2091_ = v___x_2159_;
goto v___jp_2090_;
}
}
}
v___jp_1915_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1923_, 0, v___y_1918_);
lean_ctor_set(v___x_1923_, 1, v___x_1888_);
lean_ctor_set(v___x_1923_, 2, v___y_1916_);
lean_ctor_set(v___x_1923_, 3, v_traceTask_1922_);
v___x_1924_ = lean_array_push(v_snapshotTasks_1920_, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___y_1921_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_io_promise_resolve(v___x_1925_, v_val_1889_);
if (lean_obj_tag(v_next_x3f_1913_) == 1)
{
lean_object* v_val_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_val_1927_ = lean_ctor_get(v_next_x3f_1913_, 0);
lean_inc(v_val_1927_);
lean_dec_ref(v_next_x3f_1913_);
v___x_1928_ = lean_box(0);
v___x_1929_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1928_, v_fst_1890_, v___y_1919_, v_val_1927_, v_val_1891_, v___y_1917_, v_a_1892_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; 
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1917_);
lean_dec(v_next_x3f_1913_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_fst_1890_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
}
v___jp_1931_:
{
lean_object* v_snapshotTasks_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_snapshotTasks_1938_ = lean_ctor_get(v___y_1934_, 10);
lean_inc_ref(v_snapshotTasks_1938_);
v___x_1939_ = lean_mk_empty_array_with_capacity(v___y_1937_);
lean_dec(v___y_1937_);
lean_inc_ref(v___y_1936_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1936_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_task_pure(v___x_1940_);
v___y_1916_ = v___y_1932_;
v___y_1917_ = v___y_1933_;
v___y_1918_ = v___y_1935_;
v___y_1919_ = v___y_1934_;
v_snapshotTasks_1920_ = v_snapshotTasks_1938_;
v___y_1921_ = v___y_1936_;
v_traceTask_1922_ = v___x_1941_;
goto v___jp_1915_;
}
v___jp_1942_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v_opts_1981_; uint8_t v_hasTrace_1982_; 
v___x_1972_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1958_);
v___x_1973_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1973_, 0, v___y_1952_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_ctor_set(v___x_1973_, 2, v___y_1953_);
lean_ctor_set(v___x_1973_, 3, v_traceState_1961_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*4, v_val_1891_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_reportedCmdState_1971_);
v___x_1975_ = lean_io_promise_resolve(v___x_1974_, v_val_1898_);
v___x_1976_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1960_);
lean_inc(v___y_1969_);
v___x_1977_ = l_BaseIO_chainTask___redArg(v___x_1976_, v___y_1965_, v___y_1969_, v___x_1895_);
v___x_1978_ = l_Lean_inheritedTraceOptions;
v___x_1979_ = lean_st_ref_get(v___x_1978_);
v___x_1980_ = l_List_head_x21___redArg(v___x_1902_, v_scopes_1959_);
lean_dec(v_scopes_1959_);
v_opts_1981_ = lean_ctor_get(v___x_1980_, 1);
lean_inc_ref(v_opts_1981_);
lean_dec(v___x_1980_);
v_hasTrace_1982_ = lean_ctor_get_uint8(v_opts_1981_, sizeof(void*)*1);
if (v_hasTrace_1982_ == 0)
{
lean_dec_ref(v_opts_1981_);
lean_dec(v___x_1979_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v_snapshotTasks_1962_);
lean_dec_ref(v_env_1957_);
lean_dec(v___y_1951_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_pos_1906_);
lean_dec_ref(v___f_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v___f_1903_);
lean_dec(v___x_1894_);
v___y_1932_ = v___y_1954_;
v___y_1933_ = v___y_1955_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1963_;
v___y_1936_ = v___y_1968_;
v___y_1937_ = v___y_1969_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1979_, v_opts_1981_, v___x_1983_);
lean_dec(v___x_1979_);
if (v___x_1984_ == 0)
{
lean_dec_ref(v_opts_1981_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v_snapshotTasks_1962_);
lean_dec_ref(v_env_1957_);
lean_dec(v___y_1951_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_pos_1906_);
lean_dec_ref(v___f_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v___f_1903_);
lean_dec(v___x_1894_);
v___y_1932_ = v___y_1954_;
v___y_1933_ = v___y_1955_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1963_;
v___y_1936_ = v___y_1968_;
v___y_1937_ = v___y_1969_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___f_2003_; lean_object* v___x_2004_; 
lean_inc(v___y_1969_);
v___x_1985_ = lean_task_map(v___f_1903_, v___y_1970_, v___y_1969_, v___x_1895_);
lean_inc(v___y_1954_);
lean_inc(v___y_1966_);
lean_inc(v___y_1951_);
v___x_1986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1951_);
lean_ctor_set(v___x_1986_, 1, v___y_1966_);
lean_ctor_set(v___x_1986_, 2, v___y_1954_);
lean_ctor_set(v___x_1986_, 3, v___x_1985_);
lean_inc(v___y_1969_);
v___x_1987_ = lean_task_map(v___f_1904_, v___y_1964_, v___y_1969_, v___x_1895_);
lean_inc(v___y_1954_);
lean_inc(v___y_1966_);
lean_inc(v___y_1951_);
v___x_1988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1988_, 0, v___y_1951_);
lean_ctor_set(v___x_1988_, 1, v___y_1966_);
lean_ctor_set(v___x_1988_, 2, v___y_1954_);
lean_ctor_set(v___x_1988_, 3, v___x_1987_);
lean_inc(v___y_1969_);
v___x_1989_ = lean_task_map(v___f_1905_, v___y_1967_, v___y_1969_, v___x_1895_);
lean_inc(v___y_1954_);
v___x_1990_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1951_);
lean_ctor_set(v___x_1990_, 1, v___y_1966_);
lean_ctor_set(v___x_1990_, 2, v___y_1954_);
lean_ctor_set(v___x_1990_, 3, v___x_1989_);
v___x_1991_ = lean_unsigned_to_nat(3u);
v___x_1992_ = lean_mk_empty_array_with_capacity(v___x_1991_);
v___x_1993_ = lean_array_push(v___x_1992_, v___x_1986_);
v___x_1994_ = lean_array_push(v___x_1993_, v___x_1988_);
v___x_1995_ = lean_array_push(v___x_1994_, v___x_1990_);
v___x_1996_ = l_Array_append___redArg(v___x_1995_, v_snapshotTasks_1962_);
lean_inc_ref(v___y_1968_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1968_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
lean_inc_ref(v___x_1997_);
v___x_1998_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1997_);
v___x_1999_ = lean_box_usize(v___y_1950_);
v___x_2000_ = lean_box(v___x_1895_);
v___x_2001_ = lean_box(v_val_1891_);
v___x_2002_ = lean_box(v___x_1984_);
lean_inc_ref(v_a_1892_);
v___f_2003_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2003_, 0, v___x_1894_);
lean_closure_set(v___f_2003_, 1, v___y_1948_);
lean_closure_set(v___f_2003_, 2, v___y_1949_);
lean_closure_set(v___f_2003_, 3, v___x_1999_);
lean_closure_set(v___f_2003_, 4, v___x_2000_);
lean_closure_set(v___f_2003_, 5, v_env_1957_);
lean_closure_set(v___f_2003_, 6, v___y_1944_);
lean_closure_set(v___f_2003_, 7, v___x_1978_);
lean_closure_set(v___f_2003_, 8, v_a_1892_);
lean_closure_set(v___f_2003_, 9, v_opts_1981_);
lean_closure_set(v___f_2003_, 10, v___x_1997_);
lean_closure_set(v___f_2003_, 11, v_pos_1906_);
lean_closure_set(v___f_2003_, 12, v___x_2001_);
lean_closure_set(v___f_2003_, 13, v___y_1945_);
lean_closure_set(v___f_2003_, 14, v___y_1947_);
lean_closure_set(v___f_2003_, 15, v___y_1943_);
lean_closure_set(v___f_2003_, 16, v___y_1946_);
lean_closure_set(v___f_2003_, 17, v___x_2002_);
v___x_2004_ = lean_io_bind_task(v___x_1998_, v___f_2003_, v___y_1969_, v_val_1891_);
v___y_1916_ = v___y_1954_;
v___y_1917_ = v___y_1955_;
v___y_1918_ = v___y_1963_;
v___y_1919_ = v___y_1956_;
v_snapshotTasks_1920_ = v_snapshotTasks_1962_;
v___y_1921_ = v___y_1968_;
v_traceTask_1922_ = v___x_2004_;
goto v___jp_1915_;
}
}
}
v___jp_2005_:
{
lean_object* v_env_2029_; lean_object* v_messages_2030_; lean_object* v_scopes_2031_; lean_object* v_infoState_2032_; lean_object* v_traceState_2033_; lean_object* v_snapshotTasks_2034_; 
v_env_2029_ = lean_ctor_get(v___y_2019_, 0);
lean_inc_ref(v_env_2029_);
v_messages_2030_ = lean_ctor_get(v___y_2019_, 1);
lean_inc_ref(v_messages_2030_);
v_scopes_2031_ = lean_ctor_get(v___y_2019_, 2);
lean_inc(v_scopes_2031_);
v_infoState_2032_ = lean_ctor_get(v___y_2019_, 8);
lean_inc_ref(v_infoState_2032_);
v_traceState_2033_ = lean_ctor_get(v___y_2019_, 9);
lean_inc_ref(v_traceState_2033_);
v_snapshotTasks_2034_ = lean_ctor_get(v___y_2019_, 10);
lean_inc_ref(v_snapshotTasks_2034_);
v___y_1943_ = v___y_2007_;
v___y_1944_ = v___y_2006_;
v___y_1945_ = v___y_2008_;
v___y_1946_ = v___y_2010_;
v___y_1947_ = v___y_2009_;
v___y_1948_ = v___y_2011_;
v___y_1949_ = v___y_2012_;
v___y_1950_ = v___y_2013_;
v___y_1951_ = v___y_2014_;
v___y_1952_ = v___y_2015_;
v___y_1953_ = v___y_2016_;
v___y_1954_ = v___y_2017_;
v___y_1955_ = v___y_2018_;
v___y_1956_ = v___y_2019_;
v_env_1957_ = v_env_2029_;
v_messages_1958_ = v_messages_2030_;
v_scopes_1959_ = v_scopes_2031_;
v_infoState_1960_ = v_infoState_2032_;
v_traceState_1961_ = v_traceState_2033_;
v_snapshotTasks_1962_ = v_snapshotTasks_2034_;
v___y_1963_ = v___y_2020_;
v___y_1964_ = v___y_2021_;
v___y_1965_ = v___y_2022_;
v___y_1966_ = v___y_2023_;
v___y_1967_ = v___y_2024_;
v___y_1968_ = v___y_2025_;
v___y_1969_ = v___y_2026_;
v___y_1970_ = v___y_2027_;
v_reportedCmdState_1971_ = v_reportedCmdState_2028_;
goto v___jp_1942_;
}
v___jp_2035_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; uint8_t v___x_2065_; 
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2059_);
lean_ctor_set(v___x_2060_, 1, v_val_1897_);
lean_inc_ref(v_a_1892_);
lean_inc(v___y_2049_);
lean_inc(v_pos_1906_);
lean_inc(v_fst_1907_);
v___x_2061_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1907_, v_cmdState_1908_, v_pos_1906_, v___x_2060_, v___y_2049_, v_a_1892_);
v___x_2062_ = lean_box(v_val_1891_);
v___x_2063_ = lean_box(v___x_1895_);
lean_inc(v_pos_1906_);
lean_inc_ref(v_a_1892_);
lean_inc(v___y_2042_);
lean_inc_ref(v___x_1902_);
lean_inc_ref(v___x_2061_);
lean_inc_ref(v___y_2037_);
lean_inc_ref(v___y_2038_);
v___f_2064_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2064_, 0, v___y_2038_);
lean_closure_set(v___f_2064_, 1, v___y_2037_);
lean_closure_set(v___f_2064_, 2, v___x_2062_);
lean_closure_set(v___f_2064_, 3, v_val_1899_);
lean_closure_set(v___f_2064_, 4, v___x_2061_);
lean_closure_set(v___f_2064_, 5, v___x_1902_);
lean_closure_set(v___f_2064_, 6, v___y_2042_);
lean_closure_set(v___f_2064_, 7, v___x_2063_);
lean_closure_set(v___f_2064_, 8, v_a_1892_);
lean_closure_set(v___f_2064_, 9, v_pos_1906_);
v___x_2065_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1909_, v___x_1910_);
if (v___x_2065_ == 0)
{
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2052_);
lean_dec(v_fst_1907_);
lean_inc_ref(v___x_2061_);
v___y_2006_ = v___y_2037_;
v___y_2007_ = v___y_2036_;
v___y_2008_ = v___y_2038_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2039_;
v___y_2011_ = v___y_2041_;
v___y_2012_ = v___y_2042_;
v___y_2013_ = v___y_2043_;
v___y_2014_ = v___y_2044_;
v___y_2015_ = v___y_2045_;
v___y_2016_ = v___y_2048_;
v___y_2017_ = v___y_2047_;
v___y_2018_ = v___y_2049_;
v___y_2019_ = v___x_2061_;
v___y_2020_ = v___y_2050_;
v___y_2021_ = v___y_2051_;
v___y_2022_ = v___f_2064_;
v___y_2023_ = v___y_2053_;
v___y_2024_ = v___y_2055_;
v___y_2025_ = v___y_2054_;
v___y_2026_ = v___y_2056_;
v___y_2027_ = v___y_2057_;
v_reportedCmdState_2028_ = v___x_2061_;
goto v___jp_2005_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_Parser_isTerminalCommand(v_fst_1907_);
if (v___x_2066_ == 0)
{
if (v___x_2065_ == 0)
{
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2052_);
lean_inc_ref(v___x_2061_);
v___y_2006_ = v___y_2037_;
v___y_2007_ = v___y_2036_;
v___y_2008_ = v___y_2038_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2039_;
v___y_2011_ = v___y_2041_;
v___y_2012_ = v___y_2042_;
v___y_2013_ = v___y_2043_;
v___y_2014_ = v___y_2044_;
v___y_2015_ = v___y_2045_;
v___y_2016_ = v___y_2048_;
v___y_2017_ = v___y_2047_;
v___y_2018_ = v___y_2049_;
v___y_2019_ = v___x_2061_;
v___y_2020_ = v___y_2050_;
v___y_2021_ = v___y_2051_;
v___y_2022_ = v___f_2064_;
v___y_2023_ = v___y_2053_;
v___y_2024_ = v___y_2055_;
v___y_2025_ = v___y_2054_;
v___y_2026_ = v___y_2056_;
v___y_2027_ = v___y_2057_;
v_reportedCmdState_2028_ = v___x_2061_;
goto v___jp_2005_;
}
else
{
lean_object* v_env_2067_; lean_object* v_messages_2068_; lean_object* v_scopes_2069_; lean_object* v_infoState_2070_; lean_object* v_traceState_2071_; lean_object* v_snapshotTasks_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_env_2067_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_env_2067_);
v_messages_2068_ = lean_ctor_get(v___x_2061_, 1);
lean_inc_ref(v_messages_2068_);
v_scopes_2069_ = lean_ctor_get(v___x_2061_, 2);
lean_inc(v_scopes_2069_);
v_infoState_2070_ = lean_ctor_get(v___x_2061_, 8);
lean_inc_ref(v_infoState_2070_);
v_traceState_2071_ = lean_ctor_get(v___x_2061_, 9);
lean_inc_ref(v_traceState_2071_);
v_snapshotTasks_2072_ = lean_ctor_get(v___x_2061_, 10);
lean_inc_ref(v_snapshotTasks_2072_);
v___x_2073_ = lean_mk_empty_array_with_capacity(v___y_2058_);
lean_dec(v___y_2058_);
lean_inc_ref(v___x_2073_);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_inc_n(v___y_2056_, 2);
v___x_2075_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___x_2073_);
lean_ctor_set(v___x_2075_, 2, v___y_2056_);
lean_ctor_set(v___x_2075_, 3, v___y_2056_);
lean_ctor_set_usize(v___x_2075_, 4, v___y_2046_);
v___x_2076_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2075_, 2);
v___x_2077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2075_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2079_ = l_Lean_Options_empty;
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_mk_empty_array_with_capacity(v___y_2056_);
lean_inc_ref_n(v___x_2081_, 2);
lean_inc(v___x_1894_);
v___x_2082_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2082_, 0, v___x_2078_);
lean_ctor_set(v___x_2082_, 1, v___x_2079_);
lean_ctor_set(v___x_2082_, 2, v___x_1894_);
lean_ctor_set(v___x_2082_, 3, v___x_2080_);
lean_ctor_set(v___x_2082_, 4, v___x_2080_);
lean_ctor_set(v___x_2082_, 5, v___x_2081_);
lean_ctor_set(v___x_2082_, 6, v___x_2081_);
lean_ctor_set(v___x_2082_, 7, v___x_2080_);
lean_ctor_set(v___x_2082_, 8, v___x_2080_);
lean_ctor_set(v___x_2082_, 9, v___x_2080_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*10, v_val_1891_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*10 + 1, v_val_1891_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*10 + 2, v_val_1891_);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2080_);
v___x_2084_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2085_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
lean_inc(v___x_1894_);
v___x_2086_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1894_);
v___x_2087_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2088_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_ctor_set(v___x_2088_, 2, v___x_2075_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*3, v___x_1895_);
lean_inc(v___y_2056_);
lean_inc_ref(v_env_2067_);
v___x_2089_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2089_, 0, v_env_2067_);
lean_ctor_set(v___x_2089_, 1, v___x_2077_);
lean_ctor_set(v___x_2089_, 2, v___x_2083_);
lean_ctor_set(v___x_2089_, 3, v___x_2076_);
lean_ctor_set(v___x_2089_, 4, v___x_2084_);
lean_ctor_set(v___x_2089_, 5, v___y_2056_);
lean_ctor_set(v___x_2089_, 6, v___x_2085_);
lean_ctor_set(v___x_2089_, 7, v___x_2086_);
lean_ctor_set(v___x_2089_, 8, v___x_2088_);
lean_ctor_set(v___x_2089_, 9, v___y_2052_);
lean_ctor_set(v___x_2089_, 10, v___x_2081_);
v___y_1943_ = v___y_2036_;
v___y_1944_ = v___y_2037_;
v___y_1945_ = v___y_2038_;
v___y_1946_ = v___y_2039_;
v___y_1947_ = v___y_2040_;
v___y_1948_ = v___y_2041_;
v___y_1949_ = v___y_2042_;
v___y_1950_ = v___y_2043_;
v___y_1951_ = v___y_2044_;
v___y_1952_ = v___y_2045_;
v___y_1953_ = v___y_2048_;
v___y_1954_ = v___y_2047_;
v___y_1955_ = v___y_2049_;
v___y_1956_ = v___x_2061_;
v_env_1957_ = v_env_2067_;
v_messages_1958_ = v_messages_2068_;
v_scopes_1959_ = v_scopes_2069_;
v_infoState_1960_ = v_infoState_2070_;
v_traceState_1961_ = v_traceState_2071_;
v_snapshotTasks_1962_ = v_snapshotTasks_2072_;
v___y_1963_ = v___y_2050_;
v___y_1964_ = v___y_2051_;
v___y_1965_ = v___f_2064_;
v___y_1966_ = v___y_2053_;
v___y_1967_ = v___y_2055_;
v___y_1968_ = v___y_2054_;
v___y_1969_ = v___y_2056_;
v___y_1970_ = v___y_2057_;
v_reportedCmdState_1971_ = v___x_2089_;
goto v___jp_1942_;
}
}
else
{
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2052_);
lean_inc_ref(v___x_2061_);
v___y_2006_ = v___y_2037_;
v___y_2007_ = v___y_2036_;
v___y_2008_ = v___y_2038_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2039_;
v___y_2011_ = v___y_2041_;
v___y_2012_ = v___y_2042_;
v___y_2013_ = v___y_2043_;
v___y_2014_ = v___y_2044_;
v___y_2015_ = v___y_2045_;
v___y_2016_ = v___y_2048_;
v___y_2017_ = v___y_2047_;
v___y_2018_ = v___y_2049_;
v___y_2019_ = v___x_2061_;
v___y_2020_ = v___y_2050_;
v___y_2021_ = v___y_2051_;
v___y_2022_ = v___f_2064_;
v___y_2023_ = v___y_2053_;
v___y_2024_ = v___y_2055_;
v___y_2025_ = v___y_2054_;
v___y_2026_ = v___y_2056_;
v___y_2027_ = v___y_2057_;
v_reportedCmdState_2028_ = v___x_2061_;
goto v___jp_2005_;
}
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2092_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1893_);
v___x_2093_ = l_IO_CancelToken_new();
v___x_2094_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1894_);
v___x_2095_ = l_Lean_Name_str___override(v___x_1894_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2097_ = l_Lean_Name_str___override(v___x_2095_, v___x_2096_);
v___x_2098_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2099_ = l_Lean_Name_str___override(v___x_2097_, v___x_2098_);
v___x_2100_ = l_Lean_Name_str___override(v___x_2099_, v___x_2096_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = l_Lean_Name_num___override(v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lean_Name_str___override(v___x_2102_, v___x_2096_);
v___x_2104_ = l_Lean_Name_str___override(v___x_2103_, v___x_2098_);
v___x_2105_ = l_Lean_Name_str___override(v___x_2104_, v___x_2096_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2107_ = l_Lean_Name_str___override(v___x_2105_, v___x_2106_);
v___x_2108_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2109_ = l_Lean_Name_str___override(v___x_2107_, v___x_2108_);
v___x_2110_ = l_Lean_Name_toString(v___x_2109_, v___x_1895_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_unsigned_to_nat(32u);
v___x_2113_ = ((size_t)5ULL);
v___x_2114_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref(v___x_2110_);
v___x_2115_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
lean_ctor_set(v___x_2115_, 1, v___x_2092_);
lean_ctor_set(v___x_2115_, 2, v___x_2111_);
lean_ctor_set(v___x_2115_, 3, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*4, v_val_1891_);
v___x_2116_ = l_Lean_Language_Snapshot_Diagnostics_empty;
lean_inc_ref(v___x_2110_);
v___x_2117_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2110_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
lean_ctor_set(v___x_2117_, 2, v___x_2111_);
lean_ctor_set(v___x_2117_, 3, v___x_2114_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*4, v_val_1891_);
lean_inc(v_fst_1896_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_fst_1896_);
v___x_2119_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2118_);
lean_inc(v___x_2093_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2093_);
v___x_2121_ = l_IO_Promise_result_x21___redArg(v_val_1897_);
lean_inc_ref(v___x_2121_);
lean_inc(v___x_2119_);
lean_inc_ref(v___x_2118_);
v___x_2122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2118_);
lean_ctor_set(v___x_2122_, 1, v___x_2119_);
lean_ctor_set(v___x_2122_, 2, v___x_2120_);
lean_ctor_set(v___x_2122_, 3, v___x_2121_);
v___x_2123_ = l_IO_Promise_result_x21___redArg(v_val_1898_);
lean_inc_ref(v___x_2123_);
lean_inc(v___x_1888_);
lean_inc_ref(v___x_2118_);
v___x_2124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2118_);
lean_ctor_set(v___x_2124_, 1, v___x_1888_);
lean_ctor_set(v___x_2124_, 2, v___x_2111_);
lean_ctor_set(v___x_2124_, 3, v___x_2123_);
v___x_2125_ = l_IO_Promise_result_x21___redArg(v_val_1899_);
lean_inc_ref(v___x_2125_);
lean_inc(v___x_1888_);
lean_inc_ref(v___x_2118_);
v___x_2126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2118_);
lean_ctor_set(v___x_2126_, 1, v___x_1888_);
lean_ctor_set(v___x_2126_, 2, v___x_2111_);
lean_ctor_set(v___x_2126_, 3, v___x_2125_);
v___x_2127_ = l_IO_Promise_result_x21___redArg(v_val_1889_);
lean_inc(v___x_1888_);
v___x_2128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2111_);
lean_ctor_set(v___x_2128_, 1, v___x_1888_);
lean_ctor_set(v___x_2128_, 2, v___x_2111_);
lean_ctor_set(v___x_2128_, 3, v___x_2127_);
lean_inc_ref(v___x_2117_);
v___x_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2117_);
lean_ctor_set(v___x_2129_, 1, v___x_2122_);
lean_ctor_set(v___x_2129_, 2, v___x_2124_);
lean_ctor_set(v___x_2129_, 3, v___x_2126_);
lean_ctor_set(v___x_2129_, 4, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2115_);
lean_ctor_set(v___x_2130_, 1, v_fst_1896_);
lean_ctor_set(v___x_2130_, 2, v_snd_1900_);
lean_ctor_set(v___x_2130_, 3, v___x_2129_);
lean_ctor_set(v___x_2130_, 4, v___y_2091_);
v___x_2131_ = lean_io_promise_resolve(v___x_2130_, v_prom_1901_);
if (lean_obj_tag(v_old_x3f_1911_) == 0)
{
lean_inc_ref(v___x_2110_);
lean_inc_ref(v___x_2117_);
v___y_2036_ = v___x_2117_;
v___y_2037_ = v___x_2114_;
v___y_2038_ = v___x_2110_;
v___y_2039_ = v___x_2111_;
v___y_2040_ = v___x_2111_;
v___y_2041_ = v___x_2112_;
v___y_2042_ = v___x_2101_;
v___y_2043_ = v___x_2113_;
v___y_2044_ = v___x_2118_;
v___y_2045_ = v___x_2110_;
v___y_2046_ = v___x_2113_;
v___y_2047_ = v___x_2111_;
v___y_2048_ = v___x_2111_;
v___y_2049_ = v___x_2093_;
v___y_2050_ = v___x_2111_;
v___y_2051_ = v___x_2123_;
v___y_2052_ = v___x_2114_;
v___y_2053_ = v___x_2119_;
v___y_2054_ = v___x_2117_;
v___y_2055_ = v___x_2125_;
v___y_2056_ = v___x_2101_;
v___y_2057_ = v___x_2121_;
v___y_2058_ = v___x_2112_;
v___y_2059_ = v___x_2111_;
goto v___jp_2035_;
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2143_; 
v_val_2132_ = lean_ctor_get(v_old_x3f_1911_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_old_x3f_1911_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2134_ = v_old_x3f_1911_;
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_val_2132_);
lean_dec(v_old_x3f_1911_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_elabSnap_2136_; lean_object* v_stx_2137_; lean_object* v_elabSnap_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v_elabSnap_2136_ = lean_ctor_get(v_val_2132_, 3);
lean_inc_ref(v_elabSnap_2136_);
v_stx_2137_ = lean_ctor_get(v_val_2132_, 1);
lean_inc(v_stx_2137_);
lean_dec(v_val_2132_);
v_elabSnap_2138_ = lean_ctor_get(v_elabSnap_2136_, 1);
lean_inc_ref(v_elabSnap_2138_);
lean_dec_ref(v_elabSnap_2136_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_stx_2137_);
lean_ctor_set(v___x_2139_, 1, v_elabSnap_2138_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2139_);
v___x_2141_ = v___x_2134_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_inc_ref(v___x_2110_);
lean_inc_ref(v___x_2117_);
v___y_2036_ = v___x_2117_;
v___y_2037_ = v___x_2114_;
v___y_2038_ = v___x_2110_;
v___y_2039_ = v___x_2111_;
v___y_2040_ = v___x_2111_;
v___y_2041_ = v___x_2112_;
v___y_2042_ = v___x_2101_;
v___y_2043_ = v___x_2113_;
v___y_2044_ = v___x_2118_;
v___y_2045_ = v___x_2110_;
v___y_2046_ = v___x_2113_;
v___y_2047_ = v___x_2111_;
v___y_2048_ = v___x_2111_;
v___y_2049_ = v___x_2093_;
v___y_2050_ = v___x_2111_;
v___y_2051_ = v___x_2123_;
v___y_2052_ = v___x_2114_;
v___y_2053_ = v___x_2119_;
v___y_2054_ = v___x_2117_;
v___y_2055_ = v___x_2125_;
v___y_2056_ = v___x_2101_;
v___y_2057_ = v___x_2121_;
v___y_2058_ = v___x_2112_;
v___y_2059_ = v___x_2141_;
goto v___jp_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2165_, uint8_t v_val_2166_, lean_object* v_a_2167_, lean_object* v_snd_2168_, lean_object* v___x_2169_, uint8_t v___x_2170_, lean_object* v_prom_2171_, lean_object* v___x_2172_, lean_object* v___f_2173_, lean_object* v___f_2174_, lean_object* v___f_2175_, lean_object* v_pos_2176_, lean_object* v_fst_2177_, lean_object* v_cmdState_2178_, lean_object* v_opts_2179_, lean_object* v_old_x3f_2180_, lean_object* v_parseCancelTk_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v_snapshotTasks_2194_; lean_object* v___y_2195_; lean_object* v_traceTask_2196_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; size_t v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v_env_2234_; lean_object* v_messages_2235_; lean_object* v_scopes_2236_; lean_object* v_infoState_2237_; lean_object* v_traceState_2238_; lean_object* v_snapshotTasks_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v_reportedCmdState_2249_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; size_t v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v_reportedCmdState_2308_; lean_object* v___x_2315_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; size_t v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; size_t v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v_fst_2461_; lean_object* v_snd_2462_; uint8_t v___y_2475_; uint8_t v___x_2478_; 
v___x_2183_ = lean_io_promise_new();
v___x_2184_ = lean_io_promise_new();
v___x_2185_ = lean_io_promise_new();
v___x_2186_ = lean_io_promise_new();
v___x_2315_ = l_Lean_internal_cmdlineSnapshots;
v___x_2478_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2179_, v___x_2315_);
if (v___x_2478_ == 0)
{
v___y_2475_ = v___x_2478_;
goto v___jp_2474_;
}
else
{
uint8_t v___x_2479_; 
lean_inc(v_fst_2177_);
v___x_2479_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2479_ == 0)
{
v___y_2475_ = v___x_2478_;
goto v___jp_2474_;
}
else
{
lean_inc_ref(v_fst_2165_);
lean_inc(v_fst_2177_);
v_fst_2461_ = v_fst_2177_;
v_snd_2462_ = v_fst_2165_;
goto v___jp_2460_;
}
}
v___jp_2187_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2190_);
lean_ctor_set(v___x_2197_, 1, v___y_2195_);
lean_ctor_set(v___x_2197_, 2, v___y_2192_);
lean_ctor_set(v___x_2197_, 3, v_traceTask_2196_);
v___x_2198_ = lean_array_push(v_snapshotTasks_2194_, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___y_2188_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_io_promise_resolve(v___x_2199_, v___x_2186_);
lean_dec(v___x_2186_);
if (lean_obj_tag(v___y_2189_) == 1)
{
lean_object* v_val_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_val_2201_ = lean_ctor_get(v___y_2189_, 0);
lean_inc(v_val_2201_);
lean_dec_ref(v___y_2189_);
v___x_2202_ = lean_box(0);
v___x_2203_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2202_, v_fst_2165_, v___y_2193_, v_val_2201_, v_val_2166_, v___y_2191_, v_a_2167_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; 
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2191_);
lean_dec(v___y_2189_);
lean_dec_ref(v_a_2167_);
lean_dec_ref(v_fst_2165_);
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
}
v___jp_2205_:
{
lean_object* v_snapshotTasks_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_snapshotTasks_2214_ = lean_ctor_get(v___y_2212_, 10);
lean_inc_ref(v_snapshotTasks_2214_);
v___x_2215_ = lean_mk_empty_array_with_capacity(v___y_2206_);
lean_dec(v___y_2206_);
lean_inc_ref(v___y_2207_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___y_2207_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_task_pure(v___x_2216_);
v___y_2188_ = v___y_2207_;
v___y_2189_ = v___y_2208_;
v___y_2190_ = v___y_2209_;
v___y_2191_ = v___y_2210_;
v___y_2192_ = v___y_2211_;
v___y_2193_ = v___y_2212_;
v_snapshotTasks_2194_ = v_snapshotTasks_2214_;
v___y_2195_ = v___y_2213_;
v_traceTask_2196_ = v___x_2217_;
goto v___jp_2187_;
}
v___jp_2218_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_opts_2259_; uint8_t v_hasTrace_2260_; 
v___x_2250_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2235_);
v___x_2251_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2251_, 0, v___y_2229_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
lean_ctor_set(v___x_2251_, 2, v___y_2246_);
lean_ctor_set(v___x_2251_, 3, v_traceState_2238_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*4, v_val_2166_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_reportedCmdState_2249_);
v___x_2253_ = lean_io_promise_resolve(v___x_2252_, v___x_2184_);
lean_dec(v___x_2184_);
v___x_2254_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2237_);
lean_inc(v___y_2227_);
v___x_2255_ = l_BaseIO_chainTask___redArg(v___x_2254_, v___y_2231_, v___y_2227_, v___x_2170_);
v___x_2256_ = l_Lean_inheritedTraceOptions;
v___x_2257_ = lean_st_ref_get(v___x_2256_);
v___x_2258_ = l_List_head_x21___redArg(v___x_2172_, v_scopes_2236_);
lean_dec(v_scopes_2236_);
v_opts_2259_ = lean_ctor_get(v___x_2258_, 1);
lean_inc_ref(v_opts_2259_);
lean_dec(v___x_2258_);
v_hasTrace_2260_ = lean_ctor_get_uint8(v_opts_2259_, sizeof(void*)*1);
if (v_hasTrace_2260_ == 0)
{
lean_dec_ref(v_opts_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2240_);
lean_dec_ref(v_snapshotTasks_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec(v_pos_2176_);
lean_dec_ref(v___f_2175_);
lean_dec_ref(v___f_2174_);
lean_dec_ref(v___f_2173_);
lean_dec(v___x_2169_);
v___y_2206_ = v___y_2227_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2242_;
v___y_2209_ = v___y_2230_;
v___y_2210_ = v___y_2244_;
v___y_2211_ = v___y_2232_;
v___y_2212_ = v___y_2233_;
v___y_2213_ = v___y_2248_;
goto v___jp_2205_;
}
else
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2257_, v_opts_2259_, v___x_2261_);
lean_dec(v___x_2257_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v_opts_2259_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2240_);
lean_dec_ref(v_snapshotTasks_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec(v_pos_2176_);
lean_dec_ref(v___f_2175_);
lean_dec_ref(v___f_2174_);
lean_dec_ref(v___f_2173_);
lean_dec(v___x_2169_);
v___y_2206_ = v___y_2227_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2242_;
v___y_2209_ = v___y_2230_;
v___y_2210_ = v___y_2244_;
v___y_2211_ = v___y_2232_;
v___y_2212_ = v___y_2233_;
v___y_2213_ = v___y_2248_;
goto v___jp_2205_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
lean_inc(v___y_2227_);
v___x_2263_ = lean_task_map(v___f_2173_, v___y_2247_, v___y_2227_, v___x_2170_);
lean_inc(v___y_2232_);
lean_inc(v___y_2240_);
lean_inc(v___y_2245_);
v___x_2264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2245_);
lean_ctor_set(v___x_2264_, 1, v___y_2240_);
lean_ctor_set(v___x_2264_, 2, v___y_2232_);
lean_ctor_set(v___x_2264_, 3, v___x_2263_);
lean_inc(v___y_2227_);
v___x_2265_ = lean_task_map(v___f_2174_, v___y_2228_, v___y_2227_, v___x_2170_);
lean_inc(v___y_2232_);
lean_inc(v___y_2240_);
lean_inc(v___y_2245_);
v___x_2266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2266_, 0, v___y_2245_);
lean_ctor_set(v___x_2266_, 1, v___y_2240_);
lean_ctor_set(v___x_2266_, 2, v___y_2232_);
lean_ctor_set(v___x_2266_, 3, v___x_2265_);
lean_inc(v___y_2227_);
v___x_2267_ = lean_task_map(v___f_2175_, v___y_2243_, v___y_2227_, v___x_2170_);
lean_inc(v___y_2232_);
v___x_2268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2268_, 0, v___y_2245_);
lean_ctor_set(v___x_2268_, 1, v___y_2240_);
lean_ctor_set(v___x_2268_, 2, v___y_2232_);
lean_ctor_set(v___x_2268_, 3, v___x_2267_);
v___x_2269_ = lean_unsigned_to_nat(3u);
v___x_2270_ = lean_mk_empty_array_with_capacity(v___x_2269_);
v___x_2271_ = lean_array_push(v___x_2270_, v___x_2264_);
v___x_2272_ = lean_array_push(v___x_2271_, v___x_2266_);
v___x_2273_ = lean_array_push(v___x_2272_, v___x_2268_);
v___x_2274_ = l_Array_append___redArg(v___x_2273_, v_snapshotTasks_2239_);
lean_inc_ref(v___y_2241_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___y_2241_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
lean_inc_ref(v___x_2275_);
v___x_2276_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2275_);
v___x_2277_ = lean_box_usize(v___y_2222_);
v___x_2278_ = lean_box(v___x_2170_);
v___x_2279_ = lean_box(v_val_2166_);
v___x_2280_ = lean_box(v___x_2262_);
lean_inc_ref(v_a_2167_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2281_, 0, v___x_2169_);
lean_closure_set(v___f_2281_, 1, v___y_2219_);
lean_closure_set(v___f_2281_, 2, v___y_2225_);
lean_closure_set(v___f_2281_, 3, v___x_2277_);
lean_closure_set(v___f_2281_, 4, v___x_2278_);
lean_closure_set(v___f_2281_, 5, v_env_2234_);
lean_closure_set(v___f_2281_, 6, v___y_2224_);
lean_closure_set(v___f_2281_, 7, v___x_2256_);
lean_closure_set(v___f_2281_, 8, v_a_2167_);
lean_closure_set(v___f_2281_, 9, v_opts_2259_);
lean_closure_set(v___f_2281_, 10, v___x_2275_);
lean_closure_set(v___f_2281_, 11, v_pos_2176_);
lean_closure_set(v___f_2281_, 12, v___x_2279_);
lean_closure_set(v___f_2281_, 13, v___y_2223_);
lean_closure_set(v___f_2281_, 14, v___y_2220_);
lean_closure_set(v___f_2281_, 15, v___y_2226_);
lean_closure_set(v___f_2281_, 16, v___y_2221_);
lean_closure_set(v___f_2281_, 17, v___x_2280_);
v___x_2282_ = lean_io_bind_task(v___x_2276_, v___f_2281_, v___y_2227_, v_val_2166_);
v___y_2188_ = v___y_2241_;
v___y_2189_ = v___y_2242_;
v___y_2190_ = v___y_2230_;
v___y_2191_ = v___y_2244_;
v___y_2192_ = v___y_2232_;
v___y_2193_ = v___y_2233_;
v_snapshotTasks_2194_ = v_snapshotTasks_2239_;
v___y_2195_ = v___y_2248_;
v_traceTask_2196_ = v___x_2282_;
goto v___jp_2187_;
}
}
}
v___jp_2283_:
{
lean_object* v_env_2309_; lean_object* v_messages_2310_; lean_object* v_scopes_2311_; lean_object* v_infoState_2312_; lean_object* v_traceState_2313_; lean_object* v_snapshotTasks_2314_; 
v_env_2309_ = lean_ctor_get(v___y_2298_, 0);
lean_inc_ref(v_env_2309_);
v_messages_2310_ = lean_ctor_get(v___y_2298_, 1);
lean_inc_ref(v_messages_2310_);
v_scopes_2311_ = lean_ctor_get(v___y_2298_, 2);
lean_inc(v_scopes_2311_);
v_infoState_2312_ = lean_ctor_get(v___y_2298_, 8);
lean_inc_ref(v_infoState_2312_);
v_traceState_2313_ = lean_ctor_get(v___y_2298_, 9);
lean_inc_ref(v_traceState_2313_);
v_snapshotTasks_2314_ = lean_ctor_get(v___y_2298_, 10);
lean_inc_ref(v_snapshotTasks_2314_);
v___y_2219_ = v___y_2284_;
v___y_2220_ = v___y_2285_;
v___y_2221_ = v___y_2286_;
v___y_2222_ = v___y_2287_;
v___y_2223_ = v___y_2288_;
v___y_2224_ = v___y_2290_;
v___y_2225_ = v___y_2289_;
v___y_2226_ = v___y_2291_;
v___y_2227_ = v___y_2292_;
v___y_2228_ = v___y_2293_;
v___y_2229_ = v___y_2294_;
v___y_2230_ = v___y_2295_;
v___y_2231_ = v___y_2296_;
v___y_2232_ = v___y_2297_;
v___y_2233_ = v___y_2298_;
v_env_2234_ = v_env_2309_;
v_messages_2235_ = v_messages_2310_;
v_scopes_2236_ = v_scopes_2311_;
v_infoState_2237_ = v_infoState_2312_;
v_traceState_2238_ = v_traceState_2313_;
v_snapshotTasks_2239_ = v_snapshotTasks_2314_;
v___y_2240_ = v___y_2299_;
v___y_2241_ = v___y_2300_;
v___y_2242_ = v___y_2301_;
v___y_2243_ = v___y_2302_;
v___y_2244_ = v___y_2303_;
v___y_2245_ = v___y_2304_;
v___y_2246_ = v___y_2305_;
v___y_2247_ = v___y_2306_;
v___y_2248_ = v___y_2307_;
v_reportedCmdState_2249_ = v_reportedCmdState_2308_;
goto v___jp_2218_;
}
v___jp_2316_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; uint8_t v___x_2348_; 
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___y_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2183_);
lean_inc_ref(v_a_2167_);
lean_inc(v___y_2336_);
lean_inc(v_pos_2176_);
lean_inc(v_fst_2177_);
v___x_2344_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2177_, v_cmdState_2178_, v_pos_2176_, v___x_2343_, v___y_2336_, v_a_2167_);
v___x_2345_ = lean_box(v_val_2166_);
v___x_2346_ = lean_box(v___x_2170_);
lean_inc(v_pos_2176_);
lean_inc_ref(v_a_2167_);
lean_inc(v___y_2322_);
lean_inc_ref(v___x_2172_);
lean_inc_ref(v___x_2344_);
lean_inc_ref(v___y_2323_);
lean_inc_ref(v___y_2321_);
v___f_2347_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2347_, 0, v___y_2321_);
lean_closure_set(v___f_2347_, 1, v___y_2323_);
lean_closure_set(v___f_2347_, 2, v___x_2345_);
lean_closure_set(v___f_2347_, 3, v___x_2185_);
lean_closure_set(v___f_2347_, 4, v___x_2344_);
lean_closure_set(v___f_2347_, 5, v___x_2172_);
lean_closure_set(v___f_2347_, 6, v___y_2322_);
lean_closure_set(v___f_2347_, 7, v___x_2346_);
lean_closure_set(v___f_2347_, 8, v_a_2167_);
lean_closure_set(v___f_2347_, 9, v_pos_2176_);
v___x_2348_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2179_, v___x_2315_);
if (v___x_2348_ == 0)
{
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2333_);
lean_dec(v_fst_2177_);
lean_inc_ref(v___x_2344_);
v___y_2284_ = v___y_2317_;
v___y_2285_ = v___y_2318_;
v___y_2286_ = v___y_2319_;
v___y_2287_ = v___y_2320_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v___y_2322_;
v___y_2290_ = v___y_2323_;
v___y_2291_ = v___y_2324_;
v___y_2292_ = v___y_2325_;
v___y_2293_ = v___y_2326_;
v___y_2294_ = v___y_2327_;
v___y_2295_ = v___y_2328_;
v___y_2296_ = v___f_2347_;
v___y_2297_ = v___y_2330_;
v___y_2298_ = v___x_2344_;
v___y_2299_ = v___y_2331_;
v___y_2300_ = v___y_2332_;
v___y_2301_ = v___y_2334_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2336_;
v___y_2304_ = v___y_2338_;
v___y_2305_ = v___y_2339_;
v___y_2306_ = v___y_2340_;
v___y_2307_ = v___y_2341_;
v_reportedCmdState_2308_ = v___x_2344_;
goto v___jp_2283_;
}
else
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2349_ == 0)
{
if (v___x_2348_ == 0)
{
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2333_);
lean_inc_ref(v___x_2344_);
v___y_2284_ = v___y_2317_;
v___y_2285_ = v___y_2318_;
v___y_2286_ = v___y_2319_;
v___y_2287_ = v___y_2320_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v___y_2322_;
v___y_2290_ = v___y_2323_;
v___y_2291_ = v___y_2324_;
v___y_2292_ = v___y_2325_;
v___y_2293_ = v___y_2326_;
v___y_2294_ = v___y_2327_;
v___y_2295_ = v___y_2328_;
v___y_2296_ = v___f_2347_;
v___y_2297_ = v___y_2330_;
v___y_2298_ = v___x_2344_;
v___y_2299_ = v___y_2331_;
v___y_2300_ = v___y_2332_;
v___y_2301_ = v___y_2334_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2336_;
v___y_2304_ = v___y_2338_;
v___y_2305_ = v___y_2339_;
v___y_2306_ = v___y_2340_;
v___y_2307_ = v___y_2341_;
v_reportedCmdState_2308_ = v___x_2344_;
goto v___jp_2283_;
}
else
{
lean_object* v_env_2350_; lean_object* v_messages_2351_; lean_object* v_scopes_2352_; lean_object* v_infoState_2353_; lean_object* v_traceState_2354_; lean_object* v_snapshotTasks_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_env_2350_ = lean_ctor_get(v___x_2344_, 0);
lean_inc_ref(v_env_2350_);
v_messages_2351_ = lean_ctor_get(v___x_2344_, 1);
lean_inc_ref(v_messages_2351_);
v_scopes_2352_ = lean_ctor_get(v___x_2344_, 2);
lean_inc(v_scopes_2352_);
v_infoState_2353_ = lean_ctor_get(v___x_2344_, 8);
lean_inc_ref(v_infoState_2353_);
v_traceState_2354_ = lean_ctor_get(v___x_2344_, 9);
lean_inc_ref(v_traceState_2354_);
v_snapshotTasks_2355_ = lean_ctor_get(v___x_2344_, 10);
lean_inc_ref(v_snapshotTasks_2355_);
v___x_2356_ = lean_mk_empty_array_with_capacity(v___y_2333_);
lean_dec(v___y_2333_);
lean_inc_ref(v___x_2356_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_inc_n(v___y_2325_, 2);
v___x_2358_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___x_2356_);
lean_ctor_set(v___x_2358_, 2, v___y_2325_);
lean_ctor_set(v___x_2358_, 3, v___y_2325_);
lean_ctor_set_usize(v___x_2358_, 4, v___y_2329_);
v___x_2359_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2358_, 2);
v___x_2360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2358_);
lean_ctor_set(v___x_2360_, 2, v___x_2359_);
v___x_2361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2362_ = l_Lean_Options_empty;
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_mk_empty_array_with_capacity(v___y_2325_);
lean_inc_ref_n(v___x_2364_, 2);
lean_inc(v___x_2169_);
v___x_2365_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2365_, 0, v___x_2361_);
lean_ctor_set(v___x_2365_, 1, v___x_2362_);
lean_ctor_set(v___x_2365_, 2, v___x_2169_);
lean_ctor_set(v___x_2365_, 3, v___x_2363_);
lean_ctor_set(v___x_2365_, 4, v___x_2363_);
lean_ctor_set(v___x_2365_, 5, v___x_2364_);
lean_ctor_set(v___x_2365_, 6, v___x_2364_);
lean_ctor_set(v___x_2365_, 7, v___x_2363_);
lean_ctor_set(v___x_2365_, 8, v___x_2363_);
lean_ctor_set(v___x_2365_, 9, v___x_2363_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*10, v_val_2166_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*10 + 1, v_val_2166_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*10 + 2, v_val_2166_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v___x_2363_);
v___x_2367_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2368_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
lean_inc(v___x_2169_);
v___x_2369_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2169_);
v___x_2370_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2371_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
lean_ctor_set(v___x_2371_, 2, v___x_2358_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*3, v___x_2170_);
lean_inc(v___y_2325_);
lean_inc_ref(v_env_2350_);
v___x_2372_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2372_, 0, v_env_2350_);
lean_ctor_set(v___x_2372_, 1, v___x_2360_);
lean_ctor_set(v___x_2372_, 2, v___x_2366_);
lean_ctor_set(v___x_2372_, 3, v___x_2359_);
lean_ctor_set(v___x_2372_, 4, v___x_2367_);
lean_ctor_set(v___x_2372_, 5, v___y_2325_);
lean_ctor_set(v___x_2372_, 6, v___x_2368_);
lean_ctor_set(v___x_2372_, 7, v___x_2369_);
lean_ctor_set(v___x_2372_, 8, v___x_2371_);
lean_ctor_set(v___x_2372_, 9, v___y_2335_);
lean_ctor_set(v___x_2372_, 10, v___x_2364_);
v___y_2219_ = v___y_2317_;
v___y_2220_ = v___y_2318_;
v___y_2221_ = v___y_2319_;
v___y_2222_ = v___y_2320_;
v___y_2223_ = v___y_2321_;
v___y_2224_ = v___y_2323_;
v___y_2225_ = v___y_2322_;
v___y_2226_ = v___y_2324_;
v___y_2227_ = v___y_2325_;
v___y_2228_ = v___y_2326_;
v___y_2229_ = v___y_2327_;
v___y_2230_ = v___y_2328_;
v___y_2231_ = v___f_2347_;
v___y_2232_ = v___y_2330_;
v___y_2233_ = v___x_2344_;
v_env_2234_ = v_env_2350_;
v_messages_2235_ = v_messages_2351_;
v_scopes_2236_ = v_scopes_2352_;
v_infoState_2237_ = v_infoState_2353_;
v_traceState_2238_ = v_traceState_2354_;
v_snapshotTasks_2239_ = v_snapshotTasks_2355_;
v___y_2240_ = v___y_2331_;
v___y_2241_ = v___y_2332_;
v___y_2242_ = v___y_2334_;
v___y_2243_ = v___y_2337_;
v___y_2244_ = v___y_2336_;
v___y_2245_ = v___y_2338_;
v___y_2246_ = v___y_2339_;
v___y_2247_ = v___y_2340_;
v___y_2248_ = v___y_2341_;
v_reportedCmdState_2249_ = v___x_2372_;
goto v___jp_2218_;
}
}
else
{
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2333_);
lean_inc_ref(v___x_2344_);
v___y_2284_ = v___y_2317_;
v___y_2285_ = v___y_2318_;
v___y_2286_ = v___y_2319_;
v___y_2287_ = v___y_2320_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v___y_2322_;
v___y_2290_ = v___y_2323_;
v___y_2291_ = v___y_2324_;
v___y_2292_ = v___y_2325_;
v___y_2293_ = v___y_2326_;
v___y_2294_ = v___y_2327_;
v___y_2295_ = v___y_2328_;
v___y_2296_ = v___f_2347_;
v___y_2297_ = v___y_2330_;
v___y_2298_ = v___x_2344_;
v___y_2299_ = v___y_2331_;
v___y_2300_ = v___y_2332_;
v___y_2301_ = v___y_2334_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2336_;
v___y_2304_ = v___y_2338_;
v___y_2305_ = v___y_2339_;
v___y_2306_ = v___y_2340_;
v___y_2307_ = v___y_2341_;
v_reportedCmdState_2308_ = v___x_2344_;
goto v___jp_2283_;
}
}
}
v___jp_2373_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2379_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2168_);
v___x_2380_ = l_IO_CancelToken_new();
v___x_2381_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2169_);
v___x_2382_ = l_Lean_Name_str___override(v___x_2169_, v___x_2381_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2384_ = l_Lean_Name_str___override(v___x_2382_, v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2386_ = l_Lean_Name_str___override(v___x_2384_, v___x_2385_);
v___x_2387_ = l_Lean_Name_str___override(v___x_2386_, v___x_2383_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = l_Lean_Name_num___override(v___x_2387_, v___x_2388_);
v___x_2390_ = l_Lean_Name_str___override(v___x_2389_, v___x_2383_);
v___x_2391_ = l_Lean_Name_str___override(v___x_2390_, v___x_2385_);
v___x_2392_ = l_Lean_Name_str___override(v___x_2391_, v___x_2383_);
v___x_2393_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2394_ = l_Lean_Name_str___override(v___x_2392_, v___x_2393_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2396_ = l_Lean_Name_str___override(v___x_2394_, v___x_2395_);
v___x_2397_ = l_Lean_Name_toString(v___x_2396_, v___x_2170_);
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_unsigned_to_nat(32u);
v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2399_);
lean_dec_ref(v___x_2400_);
v___x_2401_ = ((size_t)5ULL);
v___x_2402_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref(v___x_2397_);
v___x_2403_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2403_, 0, v___x_2397_);
lean_ctor_set(v___x_2403_, 1, v___x_2379_);
lean_ctor_set(v___x_2403_, 2, v___x_2398_);
lean_ctor_set(v___x_2403_, 3, v___x_2402_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*4, v_val_2166_);
v___x_2404_ = l_Lean_Language_Snapshot_Diagnostics_empty;
lean_inc_ref(v___x_2397_);
v___x_2405_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2405_, 0, v___x_2397_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
lean_ctor_set(v___x_2405_, 2, v___x_2398_);
lean_ctor_set(v___x_2405_, 3, v___x_2402_);
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*4, v_val_2166_);
lean_inc(v___y_2374_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___y_2374_);
v___x_2407_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2406_);
lean_inc(v___x_2380_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2380_);
v___x_2409_ = l_IO_Promise_result_x21___redArg(v___x_2183_);
lean_inc_ref(v___x_2409_);
lean_inc(v___x_2407_);
lean_inc_ref(v___x_2406_);
v___x_2410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2406_);
lean_ctor_set(v___x_2410_, 1, v___x_2407_);
lean_ctor_set(v___x_2410_, 2, v___x_2408_);
lean_ctor_set(v___x_2410_, 3, v___x_2409_);
v___x_2411_ = l_IO_Promise_result_x21___redArg(v___x_2184_);
lean_inc_ref(v___x_2411_);
lean_inc(v___y_2377_);
lean_inc_ref(v___x_2406_);
v___x_2412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2406_);
lean_ctor_set(v___x_2412_, 1, v___y_2377_);
lean_ctor_set(v___x_2412_, 2, v___x_2398_);
lean_ctor_set(v___x_2412_, 3, v___x_2411_);
v___x_2413_ = l_IO_Promise_result_x21___redArg(v___x_2185_);
lean_inc_ref(v___x_2413_);
lean_inc(v___y_2377_);
lean_inc_ref(v___x_2406_);
v___x_2414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2406_);
lean_ctor_set(v___x_2414_, 1, v___y_2377_);
lean_ctor_set(v___x_2414_, 2, v___x_2398_);
lean_ctor_set(v___x_2414_, 3, v___x_2413_);
v___x_2415_ = l_IO_Promise_result_x21___redArg(v___x_2186_);
lean_inc(v___y_2377_);
v___x_2416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2398_);
lean_ctor_set(v___x_2416_, 1, v___y_2377_);
lean_ctor_set(v___x_2416_, 2, v___x_2398_);
lean_ctor_set(v___x_2416_, 3, v___x_2415_);
lean_inc_ref(v___x_2405_);
v___x_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2405_);
lean_ctor_set(v___x_2417_, 1, v___x_2410_);
lean_ctor_set(v___x_2417_, 2, v___x_2412_);
lean_ctor_set(v___x_2417_, 3, v___x_2414_);
lean_ctor_set(v___x_2417_, 4, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2403_);
lean_ctor_set(v___x_2418_, 1, v___y_2374_);
lean_ctor_set(v___x_2418_, 2, v___y_2376_);
lean_ctor_set(v___x_2418_, 3, v___x_2417_);
lean_ctor_set(v___x_2418_, 4, v___y_2378_);
v___x_2419_ = lean_io_promise_resolve(v___x_2418_, v_prom_2171_);
if (lean_obj_tag(v_old_x3f_2180_) == 0)
{
lean_inc_ref(v___x_2405_);
lean_inc_ref(v___x_2397_);
v___y_2317_ = v___x_2399_;
v___y_2318_ = v___x_2398_;
v___y_2319_ = v___x_2398_;
v___y_2320_ = v___x_2401_;
v___y_2321_ = v___x_2397_;
v___y_2322_ = v___x_2388_;
v___y_2323_ = v___x_2402_;
v___y_2324_ = v___x_2405_;
v___y_2325_ = v___x_2388_;
v___y_2326_ = v___x_2411_;
v___y_2327_ = v___x_2397_;
v___y_2328_ = v___x_2398_;
v___y_2329_ = v___x_2401_;
v___y_2330_ = v___x_2398_;
v___y_2331_ = v___x_2407_;
v___y_2332_ = v___x_2405_;
v___y_2333_ = v___x_2399_;
v___y_2334_ = v___y_2375_;
v___y_2335_ = v___x_2402_;
v___y_2336_ = v___x_2380_;
v___y_2337_ = v___x_2413_;
v___y_2338_ = v___x_2406_;
v___y_2339_ = v___x_2398_;
v___y_2340_ = v___x_2409_;
v___y_2341_ = v___y_2377_;
v___y_2342_ = v___x_2398_;
goto v___jp_2316_;
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2431_; 
v_val_2420_ = lean_ctor_get(v_old_x3f_2180_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_old_x3f_2180_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2422_ = v_old_x3f_2180_;
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v_old_x3f_2180_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_elabSnap_2424_; lean_object* v_stx_2425_; lean_object* v_elabSnap_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v_elabSnap_2424_ = lean_ctor_get(v_val_2420_, 3);
lean_inc_ref(v_elabSnap_2424_);
v_stx_2425_ = lean_ctor_get(v_val_2420_, 1);
lean_inc(v_stx_2425_);
lean_dec(v_val_2420_);
v_elabSnap_2426_ = lean_ctor_get(v_elabSnap_2424_, 1);
lean_inc_ref(v_elabSnap_2426_);
lean_dec_ref(v_elabSnap_2424_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_stx_2425_);
lean_ctor_set(v___x_2427_, 1, v_elabSnap_2426_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2427_);
v___x_2429_ = v___x_2422_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_inc_ref(v___x_2405_);
lean_inc_ref(v___x_2397_);
v___y_2317_ = v___x_2399_;
v___y_2318_ = v___x_2398_;
v___y_2319_ = v___x_2398_;
v___y_2320_ = v___x_2401_;
v___y_2321_ = v___x_2397_;
v___y_2322_ = v___x_2388_;
v___y_2323_ = v___x_2402_;
v___y_2324_ = v___x_2405_;
v___y_2325_ = v___x_2388_;
v___y_2326_ = v___x_2411_;
v___y_2327_ = v___x_2397_;
v___y_2328_ = v___x_2398_;
v___y_2329_ = v___x_2401_;
v___y_2330_ = v___x_2398_;
v___y_2331_ = v___x_2407_;
v___y_2332_ = v___x_2405_;
v___y_2333_ = v___x_2399_;
v___y_2334_ = v___y_2375_;
v___y_2335_ = v___x_2402_;
v___y_2336_ = v___x_2380_;
v___y_2337_ = v___x_2413_;
v___y_2338_ = v___x_2406_;
v___y_2339_ = v___x_2398_;
v___y_2340_ = v___x_2409_;
v___y_2341_ = v___y_2377_;
v___y_2342_ = v___x_2429_;
goto v___jp_2316_;
}
}
}
}
v___jp_2432_:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2435_);
lean_inc(v_fst_2177_);
v___x_2437_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v_toProcessingContext_2439_; lean_object* v_pos_2440_; lean_object* v_endPos_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2455_; 
v___x_2438_ = lean_io_promise_new();
v_toProcessingContext_2439_ = lean_ctor_get(v_a_2167_, 0);
lean_inc_ref(v_toProcessingContext_2439_);
v_pos_2440_ = lean_ctor_get(v_fst_2165_, 0);
v_endPos_2441_ = lean_ctor_get(v_toProcessingContext_2439_, 3);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_toProcessingContext_2439_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; lean_object* v_unused_2457_; lean_object* v_unused_2458_; 
v_unused_2456_ = lean_ctor_get(v_toProcessingContext_2439_, 2);
lean_dec(v_unused_2456_);
v_unused_2457_ = lean_ctor_get(v_toProcessingContext_2439_, 1);
lean_dec(v_unused_2457_);
v_unused_2458_ = lean_ctor_get(v_toProcessingContext_2439_, 0);
lean_dec(v_unused_2458_);
v___x_2443_ = v_toProcessingContext_2439_;
v_isShared_2444_ = v_isSharedCheck_2455_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_endPos_2441_);
lean_dec(v_toProcessingContext_2439_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2455_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_inc(v___x_2438_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2438_);
v___x_2446_ = lean_box(0);
lean_inc(v_pos_2440_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_pos_2440_);
lean_ctor_set(v___x_2447_, 1, v_endPos_2441_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_parseCancelTk_2181_);
v___x_2450_ = l_IO_Promise_result_x21___redArg(v___x_2438_);
lean_dec(v___x_2438_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 3, v___x_2450_);
lean_ctor_set(v___x_2443_, 2, v___x_2449_);
lean_ctor_set(v___x_2443_, 1, v___x_2448_);
lean_ctor_set(v___x_2443_, 0, v___x_2446_);
v___x_2452_ = v___x_2443_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___y_2374_ = v___y_2433_;
v___y_2375_ = v___x_2445_;
v___y_2376_ = v___y_2434_;
v___y_2377_ = v___x_2436_;
v___y_2378_ = v___x_2453_;
goto v___jp_2373_;
}
}
}
else
{
lean_object* v___x_2459_; 
lean_dec(v_parseCancelTk_2181_);
v___x_2459_ = lean_box(0);
v___y_2374_ = v___y_2433_;
v___y_2375_ = v___x_2459_;
v___y_2376_ = v___y_2434_;
v___y_2377_ = v___x_2436_;
v___y_2378_ = v___x_2459_;
goto v___jp_2373_;
}
}
v___jp_2460_:
{
lean_object* v___x_2463_; 
lean_inc(v_fst_2177_);
v___x_2463_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2177_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_box(0);
v___y_2433_ = v_fst_2461_;
v___y_2434_ = v_snd_2462_;
v___y_2435_ = v___x_2464_;
goto v___jp_2432_;
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
v_val_2465_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_val_2465_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_inc(v_val_2465_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_val_2465_);
lean_ctor_set(v___x_2469_, 1, v_val_2465_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v___y_2433_ = v_fst_2461_;
v___y_2434_ = v_snd_2462_;
v___y_2435_ = v___x_2471_;
goto v___jp_2432_;
}
}
}
}
v___jp_2474_:
{
if (v___y_2475_ == 0)
{
lean_inc_ref(v_fst_2165_);
lean_inc(v_fst_2177_);
v_fst_2461_ = v_fst_2177_;
v_snd_2462_ = v_fst_2165_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2461_ = v___x_2476_;
v_snd_2462_ = v___x_2477_;
goto v___jp_2460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2480_ = _args[0];
lean_object* v_val_2481_ = _args[1];
lean_object* v_a_2482_ = _args[2];
lean_object* v_snd_2483_ = _args[3];
lean_object* v___x_2484_ = _args[4];
lean_object* v___x_2485_ = _args[5];
lean_object* v_prom_2486_ = _args[6];
lean_object* v___x_2487_ = _args[7];
lean_object* v___f_2488_ = _args[8];
lean_object* v___f_2489_ = _args[9];
lean_object* v___f_2490_ = _args[10];
lean_object* v_pos_2491_ = _args[11];
lean_object* v_fst_2492_ = _args[12];
lean_object* v_cmdState_2493_ = _args[13];
lean_object* v_opts_2494_ = _args[14];
lean_object* v_old_x3f_2495_ = _args[15];
lean_object* v_parseCancelTk_2496_ = _args[16];
lean_object* v___y_2497_ = _args[17];
_start:
{
uint8_t v_val_50215__boxed_2498_; uint8_t v___x_50219__boxed_2499_; lean_object* v_res_2500_; 
v_val_50215__boxed_2498_ = lean_unbox(v_val_2481_);
v___x_50219__boxed_2499_ = lean_unbox(v___x_2485_);
v_res_2500_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2480_, v_val_50215__boxed_2498_, v_a_2482_, v_snd_2483_, v___x_2484_, v___x_50219__boxed_2499_, v_prom_2486_, v___x_2487_, v___f_2488_, v___f_2489_, v___f_2490_, v_pos_2491_, v_fst_2492_, v_cmdState_2493_, v_opts_2494_, v_old_x3f_2495_, v_parseCancelTk_2496_);
lean_dec_ref(v_opts_2494_);
lean_dec(v_prom_2486_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2503_, lean_object* v_parserState_2504_, lean_object* v_cmdState_2505_, lean_object* v_prom_2506_, uint8_t v_sync_2507_, lean_object* v_parseCancelTk_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_toSnapshot_2512_; lean_object* v_stx_2513_; lean_object* v_parserState_2514_; lean_object* v_elabSnap_2515_; lean_object* v_val_2516_; lean_object* v_newParserState_2517_; lean_object* v___y_2558_; uint8_t v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; uint8_t v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; uint8_t v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; uint8_t v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2673_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; 
v___f_2600_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2601_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2602_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2603_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2503_) == 1)
{
lean_object* v_val_2748_; lean_object* v_nextCmdSnap_x3f_2749_; 
v_val_2748_ = lean_ctor_get(v_old_x3f_2503_, 0);
v_nextCmdSnap_x3f_2749_ = lean_ctor_get(v_val_2748_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2749_) == 0)
{
goto v___jp_2715_;
}
else
{
lean_object* v_toSnapshot_2750_; lean_object* v_stx_2751_; lean_object* v_parserState_2752_; lean_object* v_elabSnap_2753_; lean_object* v_val_2754_; lean_object* v___x_2755_; 
v_toSnapshot_2750_ = lean_ctor_get(v_val_2748_, 0);
v_stx_2751_ = lean_ctor_get(v_val_2748_, 1);
v_parserState_2752_ = lean_ctor_get(v_val_2748_, 2);
v_elabSnap_2753_ = lean_ctor_get(v_val_2748_, 3);
v_val_2754_ = lean_ctor_get(v_nextCmdSnap_x3f_2749_, 0);
lean_inc(v_val_2754_);
v___x_2755_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2754_);
if (lean_obj_tag(v___x_2755_) == 1)
{
lean_object* v_val_2756_; lean_object* v_nextCmdSnap_x3f_2757_; 
v_val_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_val_2756_);
lean_dec_ref(v___x_2755_);
v_nextCmdSnap_x3f_2757_ = lean_ctor_get(v_val_2756_, 4);
lean_inc(v_nextCmdSnap_x3f_2757_);
lean_dec(v_val_2756_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2757_) == 0)
{
goto v___jp_2715_;
}
else
{
lean_object* v_val_2758_; lean_object* v___x_2759_; 
v_val_2758_ = lean_ctor_get(v_nextCmdSnap_x3f_2757_, 0);
lean_inc(v_val_2758_);
lean_dec_ref(v_nextCmdSnap_x3f_2757_);
v___x_2759_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2758_);
if (lean_obj_tag(v___x_2759_) == 1)
{
lean_object* v_val_2760_; lean_object* v_parserState_2761_; lean_object* v_pos_2762_; uint8_t v___x_2763_; 
v_val_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_val_2760_);
lean_dec_ref(v___x_2759_);
v_parserState_2761_ = lean_ctor_get(v_val_2760_, 2);
lean_inc_ref(v_parserState_2761_);
lean_dec(v_val_2760_);
v_pos_2762_ = lean_ctor_get(v_parserState_2761_, 0);
lean_inc(v_pos_2762_);
lean_dec_ref(v_parserState_2761_);
v___x_2763_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2762_, v_a_2509_);
lean_dec(v_pos_2762_);
if (v___x_2763_ == 0)
{
goto v___jp_2715_;
}
else
{
lean_inc(v_val_2754_);
lean_inc_ref(v_elabSnap_2753_);
lean_inc_ref(v_parserState_2752_);
lean_inc(v_stx_2751_);
lean_inc_ref(v_toSnapshot_2750_);
lean_dec_ref(v_old_x3f_2503_);
lean_dec(v_parseCancelTk_2508_);
lean_dec_ref(v_cmdState_2505_);
lean_dec_ref(v_parserState_2504_);
lean_inc_ref(v_parserState_2752_);
v_toSnapshot_2512_ = v_toSnapshot_2750_;
v_stx_2513_ = v_stx_2751_;
v_parserState_2514_ = v_parserState_2752_;
v_elabSnap_2515_ = v_elabSnap_2753_;
v_val_2516_ = v_val_2754_;
v_newParserState_2517_ = v_parserState_2752_;
goto v___jp_2511_;
}
}
else
{
lean_dec(v___x_2759_);
goto v___jp_2715_;
}
}
}
else
{
lean_dec(v___x_2755_);
goto v___jp_2715_;
}
}
}
else
{
goto v___jp_2715_;
}
v___jp_2511_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v_resultSnap_2520_; lean_object* v_task_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2551_; 
v___x_2518_ = lean_io_promise_new();
v___x_2519_ = l_IO_CancelToken_new();
v_resultSnap_2520_ = lean_ctor_get(v_elabSnap_2515_, 2);
lean_inc_ref(v_resultSnap_2520_);
v_task_2521_ = lean_ctor_get(v_resultSnap_2520_, 3);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_resultSnap_2520_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; 
v_unused_2552_ = lean_ctor_get(v_resultSnap_2520_, 2);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_resultSnap_2520_, 1);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_resultSnap_2520_, 0);
lean_dec(v_unused_2554_);
v___x_2523_ = v_resultSnap_2520_;
v_isShared_2524_ = v_isSharedCheck_2551_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_task_2521_);
lean_dec(v_resultSnap_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2551_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v_toProcessingContext_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2549_; 
v___x_2525_ = lean_box(v_sync_2507_);
lean_inc_ref(v_a_2509_);
lean_inc(v___x_2519_);
lean_inc(v___x_2518_);
lean_inc_ref(v_newParserState_2517_);
v___f_2526_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2526_, 0, v_val_2516_);
lean_closure_set(v___f_2526_, 1, v_newParserState_2517_);
lean_closure_set(v___f_2526_, 2, v___x_2518_);
lean_closure_set(v___f_2526_, 3, v___x_2525_);
lean_closure_set(v___f_2526_, 4, v___x_2519_);
lean_closure_set(v___f_2526_, 5, v_a_2509_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = 1;
v___x_2529_ = l_BaseIO_chainTask___redArg(v_task_2521_, v___f_2526_, v___x_2527_, v___x_2528_);
v_toProcessingContext_2530_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v_a_2509_, 1);
lean_dec(v_unused_2550_);
v___x_2532_ = v_a_2509_;
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_toProcessingContext_2530_);
lean_dec(v_a_2509_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_pos_2534_; lean_object* v_endPos_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v_pos_2534_ = lean_ctor_get(v_newParserState_2517_, 0);
lean_inc(v_pos_2534_);
lean_dec_ref(v_newParserState_2517_);
v_endPos_2535_ = lean_ctor_get(v_toProcessingContext_2530_, 3);
lean_inc(v_endPos_2535_);
lean_dec_ref(v_toProcessingContext_2530_);
v___x_2536_ = lean_box(0);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 1, v_endPos_2535_);
lean_ctor_set(v___x_2532_, 0, v_pos_2534_);
v___x_2538_ = v___x_2532_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_pos_2534_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_endPos_2535_);
v___x_2538_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2519_);
v___x_2541_ = l_IO_Promise_result_x21___redArg(v___x_2518_);
lean_dec(v___x_2518_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 3, v___x_2541_);
lean_ctor_set(v___x_2523_, 2, v___x_2540_);
lean_ctor_set(v___x_2523_, 1, v___x_2539_);
lean_ctor_set(v___x_2523_, 0, v___x_2536_);
v___x_2543_ = v___x_2523_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2545_, 0, v_toSnapshot_2512_);
lean_ctor_set(v___x_2545_, 1, v_stx_2513_);
lean_ctor_set(v___x_2545_, 2, v_parserState_2514_);
lean_ctor_set(v___x_2545_, 3, v_elabSnap_2515_);
lean_ctor_set(v___x_2545_, 4, v___x_2544_);
v___x_2546_ = lean_io_promise_resolve(v___x_2545_, v_prom_2506_);
lean_dec(v_prom_2506_);
return v___x_2546_;
}
}
}
}
}
v___jp_2555_:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_box(0);
return v___x_2556_;
}
v___jp_2557_:
{
goto v___jp_2555_;
}
v___jp_2559_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2564_ = l_Lean_Name_str___override(v___y_2561_, v___x_2563_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2566_ = l_Lean_Name_str___override(v___x_2564_, v___x_2565_);
v___x_2567_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2568_ = l_Lean_Name_str___override(v___x_2566_, v___x_2567_);
v___x_2569_ = l_Lean_Name_str___override(v___x_2568_, v___x_2565_);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = l_Lean_Name_num___override(v___x_2569_, v___x_2570_);
v___x_2572_ = l_Lean_Name_str___override(v___x_2571_, v___x_2565_);
v___x_2573_ = l_Lean_Name_str___override(v___x_2572_, v___x_2567_);
v___x_2574_ = l_Lean_Name_str___override(v___x_2573_, v___x_2565_);
v___x_2575_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2576_ = l_Lean_Name_str___override(v___x_2574_, v___x_2575_);
v___x_2577_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2578_ = l_Lean_Name_str___override(v___x_2576_, v___x_2577_);
v___x_2579_ = l_Lean_Name_toString(v___x_2578_, v___y_2560_);
v___x_2580_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2583_ = 0;
v___x_2584_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2579_);
lean_ctor_set(v___x_2584_, 1, v___x_2580_);
lean_ctor_set(v___x_2584_, 2, v___x_2581_);
lean_ctor_set(v___x_2584_, 3, v___x_2582_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*4, v___x_2583_);
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref(v___x_2584_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v_cmdState_2505_);
v___x_2588_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2581_, v___x_2587_);
lean_inc_ref(v___x_2584_);
v___x_2589_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2581_, v___x_2584_);
v___x_2590_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
lean_inc_ref(v___x_2584_);
v___x_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2584_);
lean_ctor_set(v___x_2591_, 1, v___x_2586_);
lean_ctor_set(v___x_2591_, 2, v___x_2588_);
lean_ctor_set(v___x_2591_, 3, v___x_2589_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2584_);
lean_ctor_set(v___x_2592_, 1, v___x_2585_);
lean_ctor_set(v___x_2592_, 2, v___y_2562_);
lean_ctor_set(v___x_2592_, 3, v___x_2591_);
lean_ctor_set(v___x_2592_, 4, v___x_2581_);
v___x_2593_ = lean_io_promise_resolve(v___x_2592_, v_prom_2506_);
lean_dec(v_prom_2506_);
v___x_2594_ = lean_box(0);
return v___x_2594_;
}
v___jp_2595_:
{
v___y_2560_ = v___y_2596_;
v___y_2561_ = v___y_2597_;
v___y_2562_ = v___y_2598_;
goto v___jp_2559_;
}
v___jp_2604_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2621_);
v___x_2623_ = l_Lean_Parser_isTerminalCommand(v___y_2617_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_io_promise_new();
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2622_, v___y_2611_, v___y_2618_, v___y_2619_, v_a_2509_, v___y_2608_, v___y_2614_, v___y_2612_, v___y_2613_, v___y_2620_, v___y_2609_, v___y_2607_, v___y_2610_, v_prom_2506_, v___x_2603_, v___f_2602_, v___f_2601_, v___f_2600_, v___y_2616_, v___y_2606_, v_cmdState_2505_, v___y_2615_, v___y_2605_, v_old_x3f_2503_, v_parseCancelTk_2508_, v___x_2625_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2615_);
lean_dec(v_prom_2506_);
lean_dec(v___y_2609_);
lean_dec(v___y_2611_);
v___y_2558_ = v___x_2626_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_box(0);
v___x_2628_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2622_, v___y_2611_, v___y_2618_, v___y_2619_, v_a_2509_, v___y_2608_, v___y_2614_, v___y_2612_, v___y_2613_, v___y_2620_, v___y_2609_, v___y_2607_, v___y_2610_, v_prom_2506_, v___x_2603_, v___f_2602_, v___f_2601_, v___f_2600_, v___y_2616_, v___y_2606_, v_cmdState_2505_, v___y_2615_, v___y_2605_, v_old_x3f_2503_, v_parseCancelTk_2508_, v___x_2627_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2615_);
lean_dec(v_prom_2506_);
lean_dec(v___y_2609_);
lean_dec(v___y_2611_);
v___y_2558_ = v___x_2628_;
goto v___jp_2557_;
}
}
v___jp_2629_:
{
lean_object* v___x_2646_; 
lean_inc(v___y_2643_);
v___x_2646_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2643_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_box(0);
v___y_2605_ = v___y_2630_;
v___y_2606_ = v___y_2631_;
v___y_2607_ = v___y_2632_;
v___y_2608_ = v___y_2633_;
v___y_2609_ = v___y_2634_;
v___y_2610_ = v_snd_2645_;
v___y_2611_ = v___y_2635_;
v___y_2612_ = v___y_2636_;
v___y_2613_ = v_fst_2644_;
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___x_2647_;
goto v___jp_2604_;
}
else
{
lean_object* v_val_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2656_; 
v_val_2648_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2650_ = v___x_2646_;
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_val_2648_);
lean_dec(v___x_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_inc(v_val_2648_);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v_val_2648_);
lean_ctor_set(v___x_2652_, 1, v_val_2648_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2652_);
v___x_2654_ = v___x_2650_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
v___y_2605_ = v___y_2630_;
v___y_2606_ = v___y_2631_;
v___y_2607_ = v___y_2632_;
v___y_2608_ = v___y_2633_;
v___y_2609_ = v___y_2634_;
v___y_2610_ = v_snd_2645_;
v___y_2611_ = v___y_2635_;
v___y_2612_ = v___y_2636_;
v___y_2613_ = v_fst_2644_;
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___x_2654_;
goto v___jp_2604_;
}
}
}
}
v___jp_2657_:
{
if (v___y_2673_ == 0)
{
lean_inc(v___y_2671_);
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2659_;
v___y_2632_ = v___y_2660_;
v___y_2633_ = v___y_2661_;
v___y_2634_ = v___y_2662_;
v___y_2635_ = v___y_2663_;
v___y_2636_ = v___y_2664_;
v___y_2637_ = v___y_2665_;
v___y_2638_ = v___y_2666_;
v___y_2639_ = v___y_2667_;
v___y_2640_ = v___y_2668_;
v___y_2641_ = v___y_2670_;
v___y_2642_ = v___y_2669_;
v___y_2643_ = v___y_2671_;
v_fst_2644_ = v___y_2671_;
v_snd_2645_ = v___y_2672_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref(v___y_2672_);
v___x_2674_ = lean_box(0);
v___x_2675_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2659_;
v___y_2632_ = v___y_2660_;
v___y_2633_ = v___y_2661_;
v___y_2634_ = v___y_2662_;
v___y_2635_ = v___y_2663_;
v___y_2636_ = v___y_2664_;
v___y_2637_ = v___y_2665_;
v___y_2638_ = v___y_2666_;
v___y_2639_ = v___y_2667_;
v___y_2640_ = v___y_2668_;
v___y_2641_ = v___y_2670_;
v___y_2642_ = v___y_2669_;
v___y_2643_ = v___y_2671_;
v_fst_2644_ = v___x_2674_;
v_snd_2645_ = v___x_2675_;
goto v___jp_2629_;
}
}
v___jp_2676_:
{
uint8_t v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = l_IO_CancelToken_isSet(v_parseCancelTk_2508_);
v___x_2688_ = 1;
if (v___x_2687_ == 0)
{
lean_dec(v___y_2683_);
if (v_sync_2507_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2689_ = lean_io_promise_new();
v___x_2690_ = lean_io_promise_new();
v___x_2691_ = lean_io_promise_new();
v___x_2692_ = lean_io_promise_new();
v___x_2693_ = l_Lean_internal_cmdlineSnapshots;
v___x_2694_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2685_, v___x_2693_);
lean_dec_ref(v___y_2685_);
if (v___x_2694_ == 0)
{
v___y_2658_ = v___x_2693_;
v___y_2659_ = v___y_2678_;
v___y_2660_ = v___x_2691_;
v___y_2661_ = v___y_2681_;
v___y_2662_ = v___x_2690_;
v___y_2663_ = v___x_2692_;
v___y_2664_ = v___x_2688_;
v___y_2665_ = v___y_2677_;
v___y_2666_ = v___y_2679_;
v___y_2667_ = v___y_2680_;
v___y_2668_ = v___y_2682_;
v___y_2669_ = v___x_2689_;
v___y_2670_ = v___x_2687_;
v___y_2671_ = v___y_2684_;
v___y_2672_ = v___y_2686_;
v___y_2673_ = v___x_2694_;
goto v___jp_2657_;
}
else
{
uint8_t v___x_2695_; 
lean_inc(v___y_2684_);
v___x_2695_ = l_Lean_Parser_isTerminalCommand(v___y_2684_);
if (v___x_2695_ == 0)
{
v___y_2658_ = v___x_2693_;
v___y_2659_ = v___y_2678_;
v___y_2660_ = v___x_2691_;
v___y_2661_ = v___y_2681_;
v___y_2662_ = v___x_2690_;
v___y_2663_ = v___x_2692_;
v___y_2664_ = v___x_2688_;
v___y_2665_ = v___y_2677_;
v___y_2666_ = v___y_2679_;
v___y_2667_ = v___y_2680_;
v___y_2668_ = v___y_2682_;
v___y_2669_ = v___x_2689_;
v___y_2670_ = v___x_2687_;
v___y_2671_ = v___y_2684_;
v___y_2672_ = v___y_2686_;
v___y_2673_ = v___x_2694_;
goto v___jp_2657_;
}
else
{
lean_inc(v___y_2684_);
v___y_2630_ = v___x_2693_;
v___y_2631_ = v___y_2678_;
v___y_2632_ = v___x_2691_;
v___y_2633_ = v___y_2681_;
v___y_2634_ = v___x_2690_;
v___y_2635_ = v___x_2692_;
v___y_2636_ = v___x_2688_;
v___y_2637_ = v___y_2677_;
v___y_2638_ = v___y_2679_;
v___y_2639_ = v___y_2680_;
v___y_2640_ = v___y_2682_;
v___y_2641_ = v___x_2687_;
v___y_2642_ = v___x_2689_;
v___y_2643_ = v___y_2684_;
v_fst_2644_ = v___y_2684_;
v_snd_2645_ = v___y_2686_;
goto v___jp_2629_;
}
}
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
v___x_2696_ = lean_box(v___x_2687_);
v___x_2697_ = lean_box(v___x_2688_);
v___f_2698_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2698_, 0, v___y_2682_);
lean_closure_set(v___f_2698_, 1, v___x_2696_);
lean_closure_set(v___f_2698_, 2, v_a_2509_);
lean_closure_set(v___f_2698_, 3, v___y_2681_);
lean_closure_set(v___f_2698_, 4, v___y_2677_);
lean_closure_set(v___f_2698_, 5, v___x_2697_);
lean_closure_set(v___f_2698_, 6, v_prom_2506_);
lean_closure_set(v___f_2698_, 7, v___x_2603_);
lean_closure_set(v___f_2698_, 8, v___f_2602_);
lean_closure_set(v___f_2698_, 9, v___f_2601_);
lean_closure_set(v___f_2698_, 10, v___f_2600_);
lean_closure_set(v___f_2698_, 11, v___y_2680_);
lean_closure_set(v___f_2698_, 12, v___y_2678_);
lean_closure_set(v___f_2698_, 13, v_cmdState_2505_);
lean_closure_set(v___f_2698_, 14, v___y_2679_);
lean_closure_set(v___f_2698_, 15, v_old_x3f_2503_);
lean_closure_set(v___f_2698_, 16, v_parseCancelTk_2508_);
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = lean_io_as_task(v___f_2698_, v___x_2699_);
lean_dec_ref(v___x_2700_);
goto v___jp_2555_;
}
}
else
{
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v_a_2509_);
lean_dec(v_parseCancelTk_2508_);
if (lean_obj_tag(v_old_x3f_2503_) == 1)
{
lean_object* v_val_2701_; lean_object* v___x_2702_; lean_object* v_children_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_val_2701_ = lean_ctor_get(v_old_x3f_2503_, 0);
lean_inc(v_val_2701_);
lean_dec_ref(v_old_x3f_2503_);
v___x_2702_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2701_);
v_children_2703_ = lean_ctor_get(v___x_2702_, 1);
lean_inc_ref(v_children_2703_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_array_get_size(v_children_2703_);
v___x_2706_ = lean_nat_dec_lt(v___x_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_dec_ref(v_children_2703_);
v___y_2560_ = v___x_2688_;
v___y_2561_ = v___y_2683_;
v___y_2562_ = v___y_2686_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_nat_dec_le(v___x_2705_, v___x_2705_);
if (v___x_2708_ == 0)
{
if (v___x_2706_ == 0)
{
lean_dec_ref(v_children_2703_);
v___y_2560_ = v___x_2688_;
v___y_2561_ = v___y_2683_;
v___y_2562_ = v___y_2686_;
goto v___jp_2559_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2705_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2703_, v___x_2709_, v___x_2710_, v___x_2707_);
lean_dec_ref(v_children_2703_);
v___y_2596_ = v___x_2688_;
v___y_2597_ = v___y_2683_;
v___y_2598_ = v___y_2686_;
v___y_2599_ = v___x_2711_;
goto v___jp_2595_;
}
}
else
{
size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = lean_usize_of_nat(v___x_2705_);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2703_, v___x_2712_, v___x_2713_, v___x_2707_);
lean_dec_ref(v_children_2703_);
v___y_2596_ = v___x_2688_;
v___y_2597_ = v___y_2683_;
v___y_2598_ = v___y_2686_;
v___y_2599_ = v___x_2714_;
goto v___jp_2595_;
}
}
}
else
{
lean_dec(v_old_x3f_2503_);
v___y_2560_ = v___x_2688_;
v___y_2561_ = v___y_2683_;
v___y_2562_ = v___y_2686_;
goto v___jp_2559_;
}
}
}
v___jp_2715_:
{
lean_object* v_env_2716_; lean_object* v_scopes_2717_; lean_object* v___x_2718_; lean_object* v_opts_2719_; lean_object* v_currNamespace_2720_; lean_object* v_openDecls_2721_; lean_object* v___x_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v_snd_2727_; 
v_env_2716_ = lean_ctor_get(v_cmdState_2505_, 0);
v_scopes_2717_ = lean_ctor_get(v_cmdState_2505_, 2);
v___x_2718_ = l_List_head_x21___redArg(v___x_2603_, v_scopes_2717_);
v_opts_2719_ = lean_ctor_get(v___x_2718_, 1);
lean_inc_ref(v_opts_2719_);
v_currNamespace_2720_ = lean_ctor_get(v___x_2718_, 2);
lean_inc(v_currNamespace_2720_);
v_openDecls_2721_ = lean_ctor_get(v___x_2718_, 3);
lean_inc(v_openDecls_2721_);
lean_dec(v___x_2718_);
lean_inc_ref(v_opts_2719_);
lean_inc_ref(v_env_2716_);
v___x_2722_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2722_, 0, v_env_2716_);
lean_ctor_set(v___x_2722_, 1, v_opts_2719_);
lean_ctor_set(v___x_2722_, 2, v_currNamespace_2720_);
lean_ctor_set(v___x_2722_, 3, v_openDecls_2721_);
lean_inc_ref(v_parserState_2504_);
lean_inc_ref(v_a_2509_);
v___f_2723_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4), 4, 3);
lean_closure_set(v___f_2723_, 0, v_a_2509_);
lean_closure_set(v___f_2723_, 1, v___x_2722_);
lean_closure_set(v___f_2723_, 2, v_parserState_2504_);
v___x_2724_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_profileit(v___x_2724_, v_opts_2719_, v___f_2723_, v___x_2725_);
v_snd_2727_ = lean_ctor_get(v___x_2726_, 1);
lean_inc(v_snd_2727_);
if (lean_obj_tag(v_old_x3f_2503_) == 1)
{
lean_object* v_val_2728_; lean_object* v_fst_2729_; lean_object* v_fst_2730_; lean_object* v_snd_2731_; lean_object* v_pos_2732_; lean_object* v_toSnapshot_2733_; lean_object* v_stx_2734_; lean_object* v_parserState_2735_; lean_object* v_elabSnap_2736_; lean_object* v_nextCmdSnap_x3f_2737_; uint8_t v___x_2738_; 
v_val_2728_ = lean_ctor_get(v_old_x3f_2503_, 0);
v_fst_2729_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_fst_2729_);
lean_dec(v___x_2726_);
v_fst_2730_ = lean_ctor_get(v_snd_2727_, 0);
lean_inc(v_fst_2730_);
v_snd_2731_ = lean_ctor_get(v_snd_2727_, 1);
lean_inc(v_snd_2731_);
lean_dec(v_snd_2727_);
v_pos_2732_ = lean_ctor_get(v_parserState_2504_, 0);
lean_inc(v_pos_2732_);
lean_dec_ref(v_parserState_2504_);
v_toSnapshot_2733_ = lean_ctor_get(v_val_2728_, 0);
v_stx_2734_ = lean_ctor_get(v_val_2728_, 1);
v_parserState_2735_ = lean_ctor_get(v_val_2728_, 2);
v_elabSnap_2736_ = lean_ctor_get(v_val_2728_, 3);
v_nextCmdSnap_x3f_2737_ = lean_ctor_get(v_val_2728_, 4);
lean_inc(v_stx_2734_);
lean_inc(v_fst_2729_);
v___x_2738_ = l_Lean_Syntax_eqWithInfo(v_fst_2729_, v_stx_2734_);
if (v___x_2738_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2737_) == 0)
{
lean_inc(v_fst_2730_);
lean_inc_ref(v_opts_2719_);
lean_inc(v_fst_2729_);
v___y_2677_ = v___x_2725_;
v___y_2678_ = v_fst_2729_;
v___y_2679_ = v_opts_2719_;
v___y_2680_ = v_pos_2732_;
v___y_2681_ = v_snd_2731_;
v___y_2682_ = v_fst_2730_;
v___y_2683_ = v___x_2725_;
v___y_2684_ = v_fst_2729_;
v___y_2685_ = v_opts_2719_;
v___y_2686_ = v_fst_2730_;
goto v___jp_2676_;
}
else
{
lean_object* v_val_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v_val_2739_ = lean_ctor_get(v_nextCmdSnap_x3f_2737_, 0);
v___x_2740_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2739_);
v___x_2741_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2740_, v_val_2739_);
lean_inc(v_fst_2730_);
lean_inc_ref(v_opts_2719_);
lean_inc(v_fst_2729_);
v___y_2677_ = v___x_2725_;
v___y_2678_ = v_fst_2729_;
v___y_2679_ = v_opts_2719_;
v___y_2680_ = v_pos_2732_;
v___y_2681_ = v_snd_2731_;
v___y_2682_ = v_fst_2730_;
v___y_2683_ = v___x_2725_;
v___y_2684_ = v_fst_2729_;
v___y_2685_ = v_opts_2719_;
v___y_2686_ = v_fst_2730_;
goto v___jp_2676_;
}
}
else
{
lean_inc(v_val_2728_);
lean_dec(v_pos_2732_);
lean_dec(v_snd_2731_);
lean_dec(v_fst_2729_);
lean_dec_ref(v_old_x3f_2503_);
lean_dec_ref(v_opts_2719_);
lean_dec(v_parseCancelTk_2508_);
lean_dec_ref(v_cmdState_2505_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2737_) == 1)
{
lean_object* v_val_2742_; 
lean_inc_ref(v_nextCmdSnap_x3f_2737_);
lean_inc_ref(v_elabSnap_2736_);
lean_inc_ref(v_parserState_2735_);
lean_inc(v_stx_2734_);
lean_inc_ref(v_toSnapshot_2733_);
lean_dec(v_val_2728_);
v_val_2742_ = lean_ctor_get(v_nextCmdSnap_x3f_2737_, 0);
lean_inc(v_val_2742_);
lean_dec_ref(v_nextCmdSnap_x3f_2737_);
v_toSnapshot_2512_ = v_toSnapshot_2733_;
v_stx_2513_ = v_stx_2734_;
v_parserState_2514_ = v_parserState_2735_;
v_elabSnap_2515_ = v_elabSnap_2736_;
v_val_2516_ = v_val_2742_;
v_newParserState_2517_ = v_fst_2730_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2743_; 
lean_dec(v_fst_2730_);
lean_dec_ref(v_a_2509_);
v___x_2743_ = lean_io_promise_resolve(v_val_2728_, v_prom_2506_);
lean_dec(v_prom_2506_);
return v___x_2743_;
}
}
}
else
{
lean_object* v_fst_2744_; lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v_pos_2747_; 
v_fst_2744_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_fst_2744_);
lean_dec(v___x_2726_);
v_fst_2745_ = lean_ctor_get(v_snd_2727_, 0);
lean_inc(v_fst_2745_);
v_snd_2746_ = lean_ctor_get(v_snd_2727_, 1);
lean_inc(v_snd_2746_);
lean_dec(v_snd_2727_);
v_pos_2747_ = lean_ctor_get(v_parserState_2504_, 0);
lean_inc(v_pos_2747_);
lean_dec_ref(v_parserState_2504_);
lean_inc(v_fst_2745_);
lean_inc_ref(v_opts_2719_);
lean_inc(v_fst_2744_);
v___y_2677_ = v___x_2725_;
v___y_2678_ = v_fst_2744_;
v___y_2679_ = v_opts_2719_;
v___y_2680_ = v_pos_2747_;
v___y_2681_ = v_snd_2746_;
v___y_2682_ = v_fst_2745_;
v___y_2683_ = v___x_2725_;
v___y_2684_ = v_fst_2744_;
v___y_2685_ = v_opts_2719_;
v___y_2686_ = v_fst_2745_;
goto v___jp_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2764_, lean_object* v_newParserState_2765_, lean_object* v_val_2766_, uint8_t v_sync_2767_, lean_object* v_val_2768_, lean_object* v_a_2769_, lean_object* v_oldNext_2770_){
_start:
{
lean_object* v_cmdState_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_cmdState_2772_ = lean_ctor_get(v_oldResult_2764_, 1);
lean_inc_ref(v_cmdState_2772_);
lean_dec_ref(v_oldResult_2764_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_oldNext_2770_);
v___x_2774_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2773_, v_newParserState_2765_, v_cmdState_2772_, v_val_2766_, v_sync_2767_, v_val_2768_, v_a_2769_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2775_ = _args[0];
lean_object* v_val_2776_ = _args[1];
lean_object* v_fst_2777_ = _args[2];
lean_object* v_val_2778_ = _args[3];
lean_object* v_a_2779_ = _args[4];
lean_object* v_snd_2780_ = _args[5];
lean_object* v___x_2781_ = _args[6];
lean_object* v___x_2782_ = _args[7];
lean_object* v_fst_2783_ = _args[8];
lean_object* v_val_2784_ = _args[9];
lean_object* v_val_2785_ = _args[10];
lean_object* v_val_2786_ = _args[11];
lean_object* v_snd_2787_ = _args[12];
lean_object* v_prom_2788_ = _args[13];
lean_object* v___x_2789_ = _args[14];
lean_object* v___f_2790_ = _args[15];
lean_object* v___f_2791_ = _args[16];
lean_object* v___f_2792_ = _args[17];
lean_object* v_pos_2793_ = _args[18];
lean_object* v_fst_2794_ = _args[19];
lean_object* v_cmdState_2795_ = _args[20];
lean_object* v_opts_2796_ = _args[21];
lean_object* v___x_2797_ = _args[22];
lean_object* v_old_x3f_2798_ = _args[23];
lean_object* v_parseCancelTk_2799_ = _args[24];
lean_object* v_next_x3f_2800_ = _args[25];
lean_object* v___y_2801_ = _args[26];
_start:
{
uint8_t v_val_49999__boxed_2802_; uint8_t v___x_50003__boxed_2803_; lean_object* v_res_2804_; 
v_val_49999__boxed_2802_ = lean_unbox(v_val_2778_);
v___x_50003__boxed_2803_ = lean_unbox(v___x_2782_);
v_res_2804_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2775_, v_val_2776_, v_fst_2777_, v_val_49999__boxed_2802_, v_a_2779_, v_snd_2780_, v___x_2781_, v___x_50003__boxed_2803_, v_fst_2783_, v_val_2784_, v_val_2785_, v_val_2786_, v_snd_2787_, v_prom_2788_, v___x_2789_, v___f_2790_, v___f_2791_, v___f_2792_, v_pos_2793_, v_fst_2794_, v_cmdState_2795_, v_opts_2796_, v___x_2797_, v_old_x3f_2798_, v_parseCancelTk_2799_, v_next_x3f_2800_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_opts_2796_);
lean_dec(v_prom_2788_);
lean_dec(v_val_2785_);
lean_dec(v_val_2776_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2805_, lean_object* v_parserState_2806_, lean_object* v_cmdState_2807_, lean_object* v_prom_2808_, lean_object* v_sync_2809_, lean_object* v_parseCancelTk_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_sync_boxed_2813_; lean_object* v_res_2814_; 
v_sync_boxed_2813_ = lean_unbox(v_sync_2809_);
v_res_2814_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2805_, v_parserState_2806_, v_cmdState_2807_, v_prom_2808_, v_sync_boxed_2813_, v_parseCancelTk_2810_, v_a_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2815_, size_t v_i_2816_, size_t v_stop_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2815_, v_i_2816_, v_stop_2817_, v_b_2818_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2822_, lean_object* v_i_2823_, lean_object* v_stop_2824_, lean_object* v_b_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
size_t v_i_boxed_2828_; size_t v_stop_boxed_2829_; lean_object* v_res_2830_; 
v_i_boxed_2828_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_stop_boxed_2829_ = lean_unbox_usize(v_stop_2824_);
lean_dec(v_stop_2824_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2822_, v_i_boxed_2828_, v_stop_boxed_2829_, v_b_2825_, v___y_2826_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v_as_2822_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2831_, lean_object* v_opt_2832_){
_start:
{
lean_object* v_name_2833_; lean_object* v_map_2834_; lean_object* v___x_2835_; 
v_name_2833_ = lean_ctor_get(v_opt_2832_, 0);
v_map_2834_ = lean_ctor_get(v_opts_2831_, 0);
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2834_, v_name_2833_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
else
{
lean_object* v_val_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2846_; 
v_val_2837_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2839_ = v___x_2835_;
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_val_2837_);
lean_dec(v___x_2835_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
if (lean_obj_tag(v_val_2837_) == 0)
{
lean_object* v_v_2841_; lean_object* v___x_2843_; 
v_v_2841_ = lean_ctor_get(v_val_2837_, 0);
lean_inc_ref(v_v_2841_);
lean_dec_ref(v_val_2837_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v_v_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_v_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
else
{
lean_object* v___x_2845_; 
lean_del_object(v___x_2839_);
lean_dec(v_val_2837_);
v___x_2845_ = lean_box(0);
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2847_, lean_object* v_opt_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2847_, v_opt_2848_);
lean_dec_ref(v_opt_2848_);
lean_dec_ref(v_opts_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2850_, lean_object* v_x_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2850_);
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2854_, 0, v_x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2852_);
lean_ctor_set(v___x_2854_, 2, v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2861_ = l_Array_toPArray_x27___redArg(v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
if (lean_obj_tag(v_a_2862_) == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l_List_reverse___redArg(v_a_2863_);
return v___x_2864_;
}
else
{
lean_object* v_head_2865_; lean_object* v_tail_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2879_; 
v_head_2865_ = lean_ctor_get(v_a_2862_, 0);
v_tail_2866_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2868_ = v_a_2862_;
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_tail_2866_);
lean_inc(v_head_2865_);
lean_dec(v_a_2862_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2870_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_head_2865_);
v___x_2872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
v___x_2873_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v_a_2863_);
lean_ctor_set(v___x_2868_, 0, v___x_2874_);
v___x_2876_ = v___x_2868_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_a_2863_);
v___x_2876_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
v_a_2862_ = v_tail_2866_;
v_a_2863_ = v___x_2876_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2890_; double v___x_2891_; 
v___x_2890_ = lean_unsigned_to_nat(1000000000u);
v___x_2891_ = lean_float_of_nat(v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2899_ = l_Lean_MessageData_ofFormat(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2900_, lean_object* v_stx_2901_, lean_object* v_toProcessingContext_2902_, lean_object* v___x_2903_, lean_object* v_fileMap_2904_, lean_object* v_parserState_2905_, lean_object* v_a_2906_, lean_object* v___x_2907_, lean_object* v___x_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_toProcessingContext_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3135_; 
v_toProcessingContext_2911_ = lean_ctor_get(v___y_2909_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___y_2909_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___y_2909_, 1);
lean_dec(v_unused_3136_);
v___x_2913_ = v___y_2909_;
v_isShared_2914_ = v_isSharedCheck_3135_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_toProcessingContext_2911_);
lean_dec(v___y_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3135_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; 
lean_inc(v_stx_2901_);
v___x_2915_ = lean_apply_3(v_setupImports_2900_, v_stx_2901_, v_toProcessingContext_2911_, lean_box(0));
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_3126_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_3126_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_3126_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
if (lean_obj_tag(v_a_2916_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2922_; 
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2908_);
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_parserState_2905_);
lean_dec_ref(v_fileMap_2904_);
lean_dec(v___x_2903_);
lean_dec_ref(v_toProcessingContext_2902_);
lean_dec(v_stx_2901_);
v_a_2920_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v_a_2916_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_a_2920_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_3125_; 
v_a_2924_ = lean_ctor_get(v_a_2916_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_a_2916_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_2926_ = v_a_2916_;
v_isShared_2927_ = v_isSharedCheck_3125_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v_a_2916_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_3125_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v_mainModuleName_2929_; lean_object* v_package_x3f_2930_; uint8_t v_isModule_2931_; lean_object* v_imports_2932_; lean_object* v_opts_2933_; uint32_t v_trustLevel_2934_; lean_object* v_importArts_2935_; lean_object* v_plugins_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2928_ = lean_io_mono_nanos_now();
v_mainModuleName_2929_ = lean_ctor_get(v_a_2924_, 0);
lean_inc(v_mainModuleName_2929_);
v_package_x3f_2930_ = lean_ctor_get(v_a_2924_, 1);
lean_inc(v_package_x3f_2930_);
v_isModule_2931_ = lean_ctor_get_uint8(v_a_2924_, sizeof(void*)*6 + 4);
v_imports_2932_ = lean_ctor_get(v_a_2924_, 2);
lean_inc_ref(v_imports_2932_);
v_opts_2933_ = lean_ctor_get(v_a_2924_, 3);
lean_inc_ref(v_opts_2933_);
v_trustLevel_2934_ = lean_ctor_get_uint32(v_a_2924_, sizeof(void*)*6);
v_importArts_2935_ = lean_ctor_get(v_a_2924_, 4);
lean_inc(v_importArts_2935_);
v_plugins_2936_ = lean_ctor_get(v_a_2924_, 5);
lean_inc_ref(v_plugins_2936_);
lean_dec(v_a_2924_);
v___x_2937_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2901_);
v___x_2938_ = l_Lean_MessageLog_empty;
v___x_2939_ = 1;
lean_inc_ref(v_opts_2933_);
v___x_2940_ = l_Lean_Elab_processHeaderCore(v___x_2937_, v_imports_2932_, v_isModule_2931_, v_opts_2933_, v___x_2938_, v_toProcessingContext_2902_, v_trustLevel_2934_, v_plugins_2936_, v___x_2939_, v_mainModuleName_2929_, v_package_x3f_2930_, v_importArts_2935_);
lean_dec(v___x_2937_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_3116_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_3116_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_3116_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3115_; 
v_fst_2945_ = lean_ctor_get(v_a_2941_, 0);
v_snd_2946_ = lean_ctor_get(v_a_2941_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_2941_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_2948_ = v_a_2941_;
v_isShared_2949_ = v_isSharedCheck_3115_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_inc(v_fst_2945_);
lean_dec(v_a_2941_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3115_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v_traceState_2970_; 
v___x_2950_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2946_);
v___x_2951_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2946_);
v___x_2952_ = l_Lean_MessageLog_hasErrors(v_snd_2946_);
if (v___x_2952_ == 0)
{
double v___x_3065_; double v___x_3066_; double v___x_3067_; double v___x_3068_; double v___x_3069_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_del_object(v___x_2918_);
lean_dec_ref(v___x_2908_);
v___x_3065_ = lean_float_of_nat(v___x_2928_);
v___x_3066_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_3067_ = lean_float_div(v___x_3065_, v___x_3066_);
v___x_3068_ = lean_float_of_nat(v___x_2950_);
v___x_3069_ = lean_float_div(v___x_3068_, v___x_3066_);
v___x_3086_ = l_Lean_trace_profiler_output;
v___x_3087_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2933_, v___x_3086_);
if (lean_obj_tag(v___x_3087_) == 0)
{
if (v___x_2952_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2970_ = v___x_3088_;
goto v___jp_2969_;
}
else
{
goto v___jp_3070_;
}
}
else
{
lean_dec_ref(v___x_3087_);
goto v___jp_3070_;
}
v___jp_3070_:
{
uint64_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3071_ = 0ULL;
v___x_3072_ = lean_box(0);
v___x_3073_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3074_ = lean_box(0);
v___x_3075_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3076_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3076_, 0, v___x_3073_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
lean_ctor_set_float(v___x_3076_, sizeof(void*)*3, v___x_3067_);
lean_ctor_set_float(v___x_3076_, sizeof(void*)*3 + 8, v___x_3069_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3 + 16, v___x_2939_);
v___x_3077_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3078_ = lean_mk_empty_array_with_capacity(v___x_2903_);
v___x_3079_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3076_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
lean_ctor_set(v___x_3079_, 2, v___x_3078_);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3072_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_unsigned_to_nat(1u);
v___x_3082_ = lean_mk_empty_array_with_capacity(v___x_3081_);
v___x_3083_ = lean_array_push(v___x_3082_, v___x_3080_);
v___x_3084_ = l_Array_toPArray_x27___redArg(v___x_3083_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set_uint64(v___x_3085_, sizeof(void*)*1, v___x_3071_);
v_traceState_2970_ = v___x_3085_;
goto v___jp_2969_;
}
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; uint64_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_dec(v___x_2950_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec(v_fst_2945_);
lean_del_object(v___x_2943_);
lean_dec_ref(v_opts_2933_);
lean_dec(v___x_2928_);
lean_del_object(v___x_2926_);
lean_del_object(v___x_2913_);
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_parserState_2905_);
lean_dec_ref(v_fileMap_2904_);
lean_dec(v_stx_2901_);
v___x_3089_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3090_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3091_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc(v___x_2903_);
v___x_3092_ = l_Lean_Name_num___override(v___x_3091_, v___x_2903_);
v___x_3093_ = l_Lean_Name_str___override(v___x_3092_, v___x_3089_);
v___x_3094_ = l_Lean_Name_str___override(v___x_3093_, v___x_3090_);
v___x_3095_ = l_Lean_Name_str___override(v___x_3094_, v___x_3089_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3097_ = l_Lean_Name_str___override(v___x_3095_, v___x_3096_);
v___x_3098_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3099_ = l_Lean_Name_str___override(v___x_3097_, v___x_3098_);
v___x_3100_ = l_Lean_Name_toString(v___x_3099_, v___x_2939_);
v___x_3101_ = lean_box(0);
v___x_3102_ = 0ULL;
v___x_3103_ = lean_unsigned_to_nat(32u);
v___x_3104_ = lean_mk_empty_array_with_capacity(v___x_3103_);
v___x_3105_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3106_ = ((size_t)5ULL);
lean_inc(v___x_2903_);
v___x_3107_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3104_);
lean_ctor_set(v___x_3107_, 2, v___x_2903_);
lean_ctor_set(v___x_3107_, 3, v___x_2903_);
lean_ctor_set_usize(v___x_3107_, 4, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
lean_ctor_set_uint64(v___x_3108_, sizeof(void*)*1, v___x_3102_);
v___x_3109_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3109_, 0, v___x_3100_);
lean_ctor_set(v___x_3109_, 1, v___x_2951_);
lean_ctor_set(v___x_3109_, 2, v___x_3101_);
lean_ctor_set(v___x_3109_, 3, v___x_3108_);
lean_ctor_set_uint8(v___x_3109_, sizeof(void*)*4, v___x_2952_);
v___x_3110_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2908_);
v___x_3111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
lean_ctor_set(v___x_3111_, 2, v___x_3101_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_3111_);
v___x_3113_ = v___x_2918_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
v___jp_2953_:
{
lean_object* v___x_2961_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___y_2959_);
v___x_2961_ = v___x_2926_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___y_2959_);
v___x_2961_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2962_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2962_, 0, v___y_2956_);
lean_ctor_set(v___x_2962_, 1, v___x_2951_);
lean_ctor_set(v___x_2962_, 2, v___x_2961_);
lean_ctor_set(v___x_2962_, 3, v___y_2958_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*4, v___x_2952_);
v___x_2963_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2955_, v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2964_, 0, v___y_2954_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
lean_ctor_set(v___x_2964_, 2, v___y_2957_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2964_);
v___x_2966_ = v___x_2943_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
v___jp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Language_Lean_reparseOptions(v_opts_2933_);
lean_dec_ref(v_opts_2933_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_env_2978_; lean_object* v_messages_2979_; lean_object* v_scopes_2980_; lean_object* v_usedQuotCtxts_2981_; lean_object* v_nextMacroScope_2982_; lean_object* v_maxRecDepth_2983_; lean_object* v_ngen_2984_; lean_object* v_auxDeclNGen_2985_; lean_object* v_snapshotTasks_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3054_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2971_);
v___x_2973_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2903_, 3);
v___x_2974_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2903_);
lean_ctor_set(v___x_2974_, 1, v___x_2903_);
lean_ctor_set(v___x_2974_, 2, v___x_2903_);
lean_ctor_set(v___x_2974_, 3, v___x_2973_);
lean_ctor_set(v___x_2974_, 4, v___x_2973_);
lean_ctor_set(v___x_2974_, 5, v___x_2973_);
lean_ctor_set(v___x_2974_, 6, v___x_2973_);
lean_ctor_set(v___x_2974_, 7, v___x_2973_);
lean_ctor_set(v___x_2974_, 8, v___x_2973_);
v___x_2975_ = lean_io_promise_new();
v___x_2976_ = l_IO_CancelToken_new();
lean_inc(v_fst_2945_);
v___x_2977_ = l_Lean_Elab_Command_mkState(v_fst_2945_, v_snd_2946_, v_a_2972_);
v_env_2978_ = lean_ctor_get(v___x_2977_, 0);
v_messages_2979_ = lean_ctor_get(v___x_2977_, 1);
v_scopes_2980_ = lean_ctor_get(v___x_2977_, 2);
v_usedQuotCtxts_2981_ = lean_ctor_get(v___x_2977_, 3);
v_nextMacroScope_2982_ = lean_ctor_get(v___x_2977_, 4);
v_maxRecDepth_2983_ = lean_ctor_get(v___x_2977_, 5);
v_ngen_2984_ = lean_ctor_get(v___x_2977_, 6);
v_auxDeclNGen_2985_ = lean_ctor_get(v___x_2977_, 7);
v_snapshotTasks_2986_ = lean_ctor_get(v___x_2977_, 10);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3055_ = lean_ctor_get(v___x_2977_, 9);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v___x_2977_, 8);
lean_dec(v_unused_3056_);
v___x_2988_ = v___x_2977_;
v_isShared_2989_ = v_isSharedCheck_3054_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snapshotTasks_2986_);
lean_inc(v_auxDeclNGen_2985_);
lean_inc(v_ngen_2984_);
lean_inc(v_maxRecDepth_2983_);
lean_inc(v_nextMacroScope_2982_);
lean_inc(v_usedQuotCtxts_2981_);
lean_inc(v_scopes_2980_);
lean_inc(v_messages_2979_);
lean_inc(v_env_2978_);
lean_dec(v___x_2977_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3054_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = l_Lean_Options_empty;
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2996_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2996_, 0, v_fst_2945_);
lean_ctor_set(v___x_2996_, 1, v___x_2990_);
lean_ctor_set(v___x_2996_, 2, v_fileMap_2904_);
lean_ctor_set(v___x_2996_, 3, v___x_2974_);
lean_ctor_set(v___x_2996_, 4, v___x_2991_);
lean_ctor_set(v___x_2996_, 5, v___x_2992_);
lean_ctor_set(v___x_2996_, 6, v___x_2993_);
lean_ctor_set(v___x_2996_, 7, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2901_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v_stx_2901_);
lean_ctor_set(v___x_2948_, 0, v___x_2998_);
v___x_3000_ = v___x_2948_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_stx_2901_);
v___x_3000_ = v_reuseFailAlloc_3053_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
v___x_3002_ = lean_unsigned_to_nat(2u);
v___x_3003_ = l_Lean_Syntax_getArg(v_stx_2901_, v___x_3002_);
v___x_3004_ = l_Lean_Syntax_getArgs(v___x_3003_);
lean_dec(v___x_3003_);
v___x_3005_ = lean_array_to_list(v___x_3004_);
v___x_3006_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_3005_, v___x_2993_);
v___x_3007_ = l_List_toPArray_x27___redArg(v___x_3006_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 1);
lean_ctor_set(v___x_2913_, 1, v___x_3007_);
lean_ctor_set(v___x_2913_, 0, v___x_3001_);
v___x_3009_ = v___x_2913_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_2997_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_mk_empty_array_with_capacity(v___x_2994_);
v___x_3012_ = lean_array_push(v___x_3011_, v___x_3010_);
v___x_3013_ = l_Array_toPArray_x27___redArg(v___x_3012_);
lean_dec_ref(v___x_3012_);
lean_inc_ref(v___x_3013_);
v___x_3014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3014_, 0, v___x_2973_);
lean_ctor_set(v___x_3014_, 1, v___x_2973_);
lean_ctor_set(v___x_3014_, 2, v___x_3013_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*3, v___x_2939_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 9, v_traceState_2970_);
lean_ctor_set(v___x_2988_, 8, v___x_3014_);
v___x_3016_ = v___x_2988_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_env_2978_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_messages_2979_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_scopes_2980_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_usedQuotCtxts_2981_);
lean_ctor_set(v_reuseFailAlloc_3051_, 4, v_nextMacroScope_2982_);
lean_ctor_set(v_reuseFailAlloc_3051_, 5, v_maxRecDepth_2983_);
lean_ctor_set(v_reuseFailAlloc_3051_, 6, v_ngen_2984_);
lean_ctor_set(v_reuseFailAlloc_3051_, 7, v_auxDeclNGen_2985_);
lean_ctor_set(v_reuseFailAlloc_3051_, 8, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3051_, 9, v_traceState_2970_);
lean_ctor_set(v_reuseFailAlloc_3051_, 10, v_snapshotTasks_2986_);
v___x_3016_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v_size_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint64_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
lean_inc(v___x_2976_);
lean_inc(v___x_2975_);
lean_inc_ref(v___x_3016_);
v___x_3017_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2990_, v_parserState_2905_, v___x_3016_, v___x_2975_, v___x_2939_, v___x_2976_, v_a_2906_);
v___x_3018_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3019_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3020_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc(v___x_2903_);
v___x_3021_ = l_Lean_Name_num___override(v___x_3020_, v___x_2903_);
v___x_3022_ = lean_unsigned_to_nat(32u);
v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_3022_);
v___x_3024_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3025_ = ((size_t)5ULL);
lean_inc_n(v___x_2903_, 2);
v___x_3026_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3023_);
lean_ctor_set(v___x_3026_, 2, v___x_2903_);
lean_ctor_set(v___x_3026_, 3, v___x_2903_);
lean_ctor_set_usize(v___x_3026_, 4, v___x_3025_);
v_size_3027_ = lean_ctor_get(v___x_3013_, 2);
lean_inc(v_size_3027_);
v___x_3028_ = l_Lean_Name_str___override(v___x_3021_, v___x_3018_);
v___x_3029_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2907_);
v___x_3030_ = l_Lean_Name_str___override(v___x_3028_, v___x_3019_);
v___x_3031_ = l_Lean_Name_str___override(v___x_3030_, v___x_3018_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3033_ = l_Lean_Name_str___override(v___x_3031_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3035_ = l_Lean_Name_str___override(v___x_3033_, v___x_3034_);
v___x_3036_ = l_Lean_Name_toString(v___x_3035_, v___x_2939_);
v___x_3037_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3038_ = 0ULL;
v___x_3039_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3039_, 0, v___x_3026_);
lean_ctor_set_uint64(v___x_3039_, sizeof(void*)*1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_2976_);
v___x_3041_ = l_IO_Promise_result_x21___redArg(v___x_2975_);
lean_dec(v___x_2975_);
v___x_3042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3042_, 0, v___x_2907_);
lean_ctor_set(v___x_3042_, 1, v___x_3029_);
lean_ctor_set(v___x_3042_, 2, v___x_3040_);
lean_ctor_set(v___x_3042_, 3, v___x_3041_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3016_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_inc_ref(v___x_3039_);
lean_inc_ref(v___x_3036_);
v___x_3045_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3045_, 0, v___x_3036_);
lean_ctor_set(v___x_3045_, 1, v___x_3037_);
lean_ctor_set(v___x_3045_, 2, v___x_2990_);
lean_ctor_set(v___x_3045_, 3, v___x_3039_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*4, v___x_2952_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_stx_2901_);
v___x_3047_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3048_ = lean_nat_dec_lt(v___x_2903_, v_size_3027_);
lean_dec(v_size_3027_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v___x_3013_);
lean_dec(v___x_2903_);
v___x_3049_ = l_outOfBounds___redArg(v___x_3047_);
v___y_2954_ = v___x_3045_;
v___y_2955_ = v___x_3046_;
v___y_2956_ = v___x_3036_;
v___y_2957_ = v___x_3044_;
v___y_2958_ = v___x_3039_;
v___y_2959_ = v___x_3049_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3047_, v___x_3013_, v___x_2903_);
lean_dec(v___x_2903_);
v___y_2954_ = v___x_3045_;
v___y_2955_ = v___x_3046_;
v___y_2956_ = v___x_3036_;
v___y_2957_ = v___x_3044_;
v___y_2958_ = v___x_3039_;
v___y_2959_ = v___x_3050_;
goto v___jp_2953_;
}
}
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v_traceState_2970_);
lean_dec_ref(v___x_2951_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec(v_fst_2945_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2926_);
lean_del_object(v___x_2913_);
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_parserState_2905_);
lean_dec_ref(v_fileMap_2904_);
lean_dec(v___x_2903_);
lean_dec(v_stx_2901_);
v_a_3057_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2971_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2971_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_opts_2933_);
lean_dec(v___x_2928_);
lean_del_object(v___x_2926_);
lean_del_object(v___x_2918_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2908_);
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_parserState_2905_);
lean_dec_ref(v_fileMap_2904_);
lean_dec(v___x_2903_);
lean_dec(v_stx_2901_);
v_a_3117_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_2940_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_2940_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2908_);
lean_dec(v___x_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_parserState_2905_);
lean_dec_ref(v_fileMap_2904_);
lean_dec(v___x_2903_);
lean_dec_ref(v_toProcessingContext_2902_);
lean_dec(v_stx_2901_);
v_a_3127_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_2915_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_2915_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3137_, lean_object* v_stx_3138_, lean_object* v_toProcessingContext_3139_, lean_object* v___x_3140_, lean_object* v_fileMap_3141_, lean_object* v_parserState_3142_, lean_object* v_a_3143_, lean_object* v___x_3144_, lean_object* v___x_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3137_, v_stx_3138_, v_toProcessingContext_3139_, v___x_3140_, v_fileMap_3141_, v_parserState_3142_, v_a_3143_, v___x_3144_, v___x_3145_, v___y_3146_);
return v_res_3148_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___f_3150_; 
v___x_3149_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3150_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3150_, 0, v___x_3149_);
return v___f_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3151_, lean_object* v_stx_3152_, lean_object* v_parserState_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_toProcessingContext_3156_; lean_object* v_fileMap_3157_; lean_object* v_endPos_3158_; lean_object* v___x_3159_; lean_object* v___f_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___f_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_toProcessingContext_3156_ = lean_ctor_get(v_a_3154_, 0);
v_fileMap_3157_ = lean_ctor_get(v_toProcessingContext_3156_, 2);
v_endPos_3158_ = lean_ctor_get(v_toProcessingContext_3156_, 3);
v___x_3159_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3160_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3154_);
lean_inc_ref(v_fileMap_3157_);
lean_inc_ref(v_toProcessingContext_3156_);
v___f_3163_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 11, 9);
lean_closure_set(v___f_3163_, 0, v_setupImports_3151_);
lean_closure_set(v___f_3163_, 1, v_stx_3152_);
lean_closure_set(v___f_3163_, 2, v_toProcessingContext_3156_);
lean_closure_set(v___f_3163_, 3, v___x_3162_);
lean_closure_set(v___f_3163_, 4, v_fileMap_3157_);
lean_closure_set(v___f_3163_, 5, v_parserState_3153_);
lean_closure_set(v___f_3163_, 6, v_a_3154_);
lean_closure_set(v___f_3163_, 7, v___x_3161_);
lean_closure_set(v___f_3163_, 8, v___x_3159_);
lean_inc(v_endPos_3158_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v_endPos_3158_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
v___x_3166_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3166_, 0, lean_box(0));
lean_closure_set(v___x_3166_, 1, v___f_3160_);
lean_closure_set(v___x_3166_, 2, v___f_3163_);
lean_closure_set(v___x_3166_, 3, v_a_3154_);
v___x_3167_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3161_, v___x_3161_, v___x_3165_, v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3168_, lean_object* v_stx_3169_, lean_object* v_parserState_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3168_, v_stx_3169_, v_parserState_3170_, v_a_3171_);
return v_res_3173_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_box(0);
v___x_3175_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = 1;
v___x_3181_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3182_ = l_Lean_Name_toString(v___x_3181_, v___x_3180_);
return v___x_3182_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3183_ = 0;
v___x_3184_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3185_ = lean_box(0);
v___x_3186_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3187_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3188_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v___x_3186_);
lean_ctor_set(v___x_3188_, 2, v___x_3185_);
lean_ctor_set(v___x_3188_, 3, v___x_3184_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*4, v___x_3183_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3189_, lean_object* v_cmdState_3190_, lean_object* v_a_3191_, lean_object* v_toSnapshot_3192_, lean_object* v_newStx_3193_, lean_object* v_oldCmd_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v_diagnostics_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3223_; 
v___x_3196_ = lean_io_promise_new();
v___x_3197_ = l_IO_CancelToken_new();
v___x_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_oldCmd_3194_);
v___x_3199_ = 1;
lean_inc(v___x_3197_);
lean_inc(v___x_3196_);
lean_inc_ref(v_cmdState_3190_);
v___x_3200_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3198_, v_newParserState_3189_, v_cmdState_3190_, v___x_3196_, v___x_3199_, v___x_3197_, v_a_3191_);
v_diagnostics_3201_ = lean_ctor_get(v_toSnapshot_3192_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_toSnapshot_3192_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; lean_object* v_unused_3225_; lean_object* v_unused_3226_; 
v_unused_3224_ = lean_ctor_get(v_toSnapshot_3192_, 3);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_toSnapshot_3192_, 2);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_toSnapshot_3192_, 0);
lean_dec(v_unused_3226_);
v___x_3203_ = v_toSnapshot_3192_;
v_isShared_3204_ = v_isSharedCheck_3223_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_diagnostics_3201_);
lean_dec(v_toSnapshot_3192_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3223_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3207_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3208_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3197_);
v___x_3210_ = l_IO_Promise_result_x21___redArg(v___x_3196_);
lean_dec(v___x_3196_);
v___x_3211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3205_);
lean_ctor_set(v___x_3211_, 1, v___x_3206_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_cmdState_3190_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
v___x_3214_ = 0;
v___x_3215_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_newStx_3193_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 3, v___x_3208_);
lean_ctor_set(v___x_3203_, 2, v___x_3205_);
lean_ctor_set(v___x_3203_, 0, v___x_3207_);
v___x_3218_ = v___x_3203_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_diagnostics_3201_);
lean_ctor_set(v_reuseFailAlloc_3222_, 2, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3222_, 3, v___x_3208_);
v___x_3218_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*4, v___x_3214_);
v___x_3219_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3216_, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3215_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
lean_ctor_set(v___x_3220_, 2, v___x_3213_);
v___x_3221_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3205_, v___x_3220_);
return v___x_3221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3227_, lean_object* v_cmdState_3228_, lean_object* v_a_3229_, lean_object* v_toSnapshot_3230_, lean_object* v_newStx_3231_, lean_object* v_oldCmd_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3227_, v_cmdState_3228_, v_a_3229_, v_toSnapshot_3230_, v_newStx_3231_, v_oldCmd_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3235_, lean_object* v_a_3236_, lean_object* v_newStx_3237_, lean_object* v___x_3238_, lean_object* v_oldProcessed_3239_){
_start:
{
lean_object* v_result_x3f_3241_; 
v_result_x3f_3241_ = lean_ctor_get(v_oldProcessed_3239_, 2);
if (lean_obj_tag(v_result_x3f_3241_) == 1)
{
lean_object* v_val_3242_; lean_object* v_firstCmdSnap_3243_; lean_object* v_toSnapshot_3244_; lean_object* v_cmdState_3245_; lean_object* v_stx_x3f_3246_; lean_object* v___f_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; lean_object* v___x_3250_; 
v_val_3242_ = lean_ctor_get(v_result_x3f_3241_, 0);
lean_inc(v_val_3242_);
v_firstCmdSnap_3243_ = lean_ctor_get(v_val_3242_, 1);
lean_inc_ref(v_firstCmdSnap_3243_);
v_toSnapshot_3244_ = lean_ctor_get(v_oldProcessed_3239_, 0);
lean_inc_ref(v_toSnapshot_3244_);
lean_dec_ref(v_oldProcessed_3239_);
v_cmdState_3245_ = lean_ctor_get(v_val_3242_, 0);
lean_inc_ref(v_cmdState_3245_);
lean_dec(v_val_3242_);
v_stx_x3f_3246_ = lean_ctor_get(v_firstCmdSnap_3243_, 0);
lean_inc(v_stx_x3f_3246_);
v___f_3247_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3247_, 0, v_newParserState_3235_);
lean_closure_set(v___f_3247_, 1, v_cmdState_3245_);
lean_closure_set(v___f_3247_, 2, v_a_3236_);
lean_closure_set(v___f_3247_, 3, v_toSnapshot_3244_);
lean_closure_set(v___f_3247_, 4, v_newStx_3237_);
v___x_3248_ = lean_box(0);
v___x_3249_ = 1;
v___x_3250_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3243_, v___f_3247_, v_stx_x3f_3246_, v___x_3238_, v___x_3248_, v___x_3249_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v___x_3238_);
lean_dec_ref(v_a_3236_);
lean_dec_ref(v_newParserState_3235_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_newStx_3237_);
v___x_3252_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3251_, v_oldProcessed_3239_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3253_, lean_object* v_a_3254_, lean_object* v_newStx_3255_, lean_object* v___x_3256_, lean_object* v_oldProcessed_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3253_, v_a_3254_, v_newStx_3255_, v___x_3256_, v_oldProcessed_3257_);
return v_res_3259_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3260_ = 0;
v___x_3261_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3262_ = lean_box(0);
v___x_3263_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3264_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3263_);
lean_ctor_set(v___x_3265_, 2, v___x_3262_);
lean_ctor_set(v___x_3265_, 3, v___x_3261_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*4, v___x_3260_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3266_, lean_object* v_a_3267_, lean_object* v_old_3268_, lean_object* v_newStx_3269_, lean_object* v_newParserState_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_result_x3f_3273_; 
v_result_x3f_3273_ = lean_ctor_get(v_old_3268_, 4);
lean_inc(v_result_x3f_3273_);
if (lean_obj_tag(v_result_x3f_3273_) == 1)
{
lean_object* v_val_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3328_; 
v_val_3274_ = lean_ctor_get(v_result_x3f_3273_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_result_x3f_3273_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3276_ = v_result_x3f_3273_;
v_isShared_3277_ = v_isSharedCheck_3328_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_val_3274_);
lean_dec(v_result_x3f_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3328_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_processedSnap_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3326_; 
v_processedSnap_3278_ = lean_ctor_get(v_val_3274_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_val_3274_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v_val_3274_, 0);
lean_dec(v_unused_3327_);
v___x_3280_ = v_val_3274_;
v_isShared_3281_ = v_isSharedCheck_3326_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_processedSnap_3278_);
lean_dec(v_val_3274_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3326_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_toSnapshot_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3321_; 
v_toSnapshot_3282_ = lean_ctor_get(v_old_3268_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_old_3268_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3322_ = lean_ctor_get(v_old_3268_, 4);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_old_3268_, 3);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_old_3268_, 2);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_old_3268_, 1);
lean_dec(v_unused_3325_);
v___x_3284_ = v_old_3268_;
v_isShared_3285_ = v_isSharedCheck_3321_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_toSnapshot_3282_);
lean_dec(v_old_3268_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3321_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_pos_3286_; lean_object* v_endPos_3287_; lean_object* v_stx_x3f_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v_diagnostics_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3317_; 
v_pos_3286_ = lean_ctor_get(v_newParserState_3270_, 0);
v_endPos_3287_ = lean_ctor_get(v_toProcessingContext_3266_, 3);
v_stx_x3f_3288_ = lean_ctor_get(v_processedSnap_3278_, 0);
lean_inc(v_stx_x3f_3288_);
lean_inc(v_endPos_3287_);
lean_inc(v_pos_3286_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v_pos_3286_);
lean_ctor_set(v___x_3289_, 1, v_endPos_3287_);
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_inc_ref(v___x_3290_);
lean_inc(v_newStx_3269_);
lean_inc_ref(v_newParserState_3270_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3291_, 0, v_newParserState_3270_);
lean_closure_set(v___f_3291_, 1, v_a_3267_);
lean_closure_set(v___f_3291_, 2, v_newStx_3269_);
lean_closure_set(v___f_3291_, 3, v___x_3290_);
v___x_3292_ = lean_box(0);
v___x_3293_ = 1;
v___x_3294_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3278_, v___f_3291_, v_stx_x3f_3288_, v___x_3290_, v___x_3292_, v___x_3293_);
v_diagnostics_3295_ = lean_ctor_get(v_toSnapshot_3282_, 1);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_toSnapshot_3282_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3318_ = lean_ctor_get(v_toSnapshot_3282_, 3);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_toSnapshot_3282_, 2);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_toSnapshot_3282_, 0);
lean_dec(v_unused_3320_);
v___x_3297_ = v_toSnapshot_3282_;
v_isShared_3298_ = v_isSharedCheck_3317_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_diagnostics_3295_);
lean_dec(v_toSnapshot_3282_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3317_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3300_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3294_);
lean_ctor_set(v___x_3280_, 0, v_newParserState_3270_);
v___x_3302_ = v___x_3280_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_newParserState_3270_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3294_);
v___x_3302_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3304_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3302_);
v___x_3304_ = v___x_3276_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
uint8_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3305_ = 0;
v___x_3306_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3269_);
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v_newStx_3269_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 3, v___x_3300_);
lean_ctor_set(v___x_3297_, 2, v___x_3292_);
lean_ctor_set(v___x_3297_, 0, v___x_3299_);
v___x_3309_ = v___x_3297_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_diagnostics_3295_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___x_3300_);
v___x_3309_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3312_; 
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*4, v___x_3305_);
v___x_3310_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3307_, v___x_3309_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 4, v___x_3304_);
lean_ctor_set(v___x_3284_, 3, v_newStx_3269_);
lean_ctor_set(v___x_3284_, 2, v_toProcessingContext_3266_);
lean_ctor_set(v___x_3284_, 1, v___x_3310_);
lean_ctor_set(v___x_3284_, 0, v___x_3306_);
v___x_3312_ = v___x_3284_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_toProcessingContext_3266_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_newStx_3269_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v___x_3304_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
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
lean_dec(v_result_x3f_3273_);
lean_dec_ref(v_newParserState_3270_);
lean_dec(v_newStx_3269_);
lean_dec_ref(v_a_3267_);
lean_dec_ref(v_toProcessingContext_3266_);
return v_old_3268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3329_, lean_object* v_a_3330_, lean_object* v_old_3331_, lean_object* v_newStx_3332_, lean_object* v_newParserState_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3329_, v_a_3330_, v_old_3331_, v_newStx_3332_, v_newParserState_3333_, v___y_3334_);
lean_dec_ref(v___y_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3337_, lean_object* v_setupImports_3338_, lean_object* v_old_x3f_3339_, lean_object* v___f_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
lean_inc_ref(v_toProcessingContext_3337_);
v___x_3343_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3337_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3413_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3413_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3413_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3412_; 
v_snd_3348_ = lean_ctor_get(v_a_3344_, 1);
lean_inc(v_snd_3348_);
v_fst_3349_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_fst_3349_);
lean_dec(v_a_3344_);
v_fst_3350_ = lean_ctor_get(v_snd_3348_, 0);
v_snd_3351_ = lean_ctor_get(v_snd_3348_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_snd_3348_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3353_ = v_snd_3348_;
v_isShared_3354_ = v_isSharedCheck_3412_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_snd_3351_);
lean_inc(v_fst_3350_);
lean_dec(v_snd_3348_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3412_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Lean_MessageLog_hasErrors(v_snd_3351_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___y_3358_; 
lean_inc(v_fst_3349_);
v___x_3356_ = l_Lean_Syntax_unsetTrailing(v_fst_3349_);
if (lean_obj_tag(v_old_x3f_3339_) == 1)
{
lean_object* v_val_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3395_; 
v_val_3379_ = lean_ctor_get(v_old_x3f_3339_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_old_x3f_3339_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3381_ = v_old_x3f_3339_;
v_isShared_3382_ = v_isSharedCheck_3395_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_val_3379_);
lean_dec(v_old_x3f_3339_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3395_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_stx_3383_; lean_object* v_result_x3f_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_stx_3383_ = lean_ctor_get(v_val_3379_, 3);
v_result_x3f_3384_ = lean_ctor_get(v_val_3379_, 4);
lean_inc(v_stx_3383_);
v___x_3385_ = l_Lean_Syntax_unsetTrailing(v_stx_3383_);
lean_inc(v___x_3356_);
v___x_3386_ = l_Lean_Syntax_eqWithInfo(v___x_3356_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_inc(v_result_x3f_3384_);
lean_del_object(v___x_3381_);
lean_dec(v_val_3379_);
lean_dec_ref(v___f_3340_);
if (lean_obj_tag(v_result_x3f_3384_) == 0)
{
v___y_3358_ = v___y_3341_;
goto v___jp_3357_;
}
else
{
lean_object* v_val_3387_; lean_object* v_processedSnap_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_val_3387_ = lean_ctor_get(v_result_x3f_3384_, 0);
lean_inc(v_val_3387_);
lean_dec_ref(v_result_x3f_3384_);
v_processedSnap_3388_ = lean_ctor_get(v_val_3387_, 1);
lean_inc_ref(v_processedSnap_3388_);
lean_dec(v_val_3387_);
v___x_3389_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3390_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3389_, v_processedSnap_3388_);
v___y_3358_ = v___y_3341_;
goto v___jp_3357_;
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
lean_dec(v___x_3356_);
lean_del_object(v___x_3353_);
lean_dec(v_snd_3351_);
lean_del_object(v___x_3346_);
lean_dec_ref(v_setupImports_3338_);
lean_dec_ref(v_toProcessingContext_3337_);
v___x_3391_ = lean_apply_5(v___f_3340_, v_val_3379_, v_fst_3349_, v_fst_3350_, v___y_3341_, lean_box(0));
if (v_isShared_3382_ == 0)
{
lean_ctor_set_tag(v___x_3381_, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3391_);
v___x_3393_ = v___x_3381_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_dec_ref(v___f_3340_);
lean_dec(v_old_x3f_3339_);
v___y_3358_ = v___y_3341_;
goto v___jp_3357_;
}
v___jp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3359_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3351_);
lean_inc(v_fst_3350_);
v___x_3360_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3338_, v___x_3356_, v_fst_3350_, v___y_3358_);
v___x_3361_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3362_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_unsigned_to_nat(32u);
v___x_3365_ = lean_mk_empty_array_with_capacity(v___x_3364_);
lean_dec_ref(v___x_3365_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3360_);
v___x_3368_ = v___x_3353_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_fst_3350_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3360_);
v___x_3368_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3370_, 0, v___x_3361_);
lean_ctor_set(v___x_3370_, 1, v___x_3362_);
lean_ctor_set(v___x_3370_, 2, v___x_3363_);
lean_ctor_set(v___x_3370_, 3, v___x_3366_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*4, v___x_3355_);
lean_inc(v_fst_3349_);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v_fst_3349_);
v___x_3372_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3372_, 0, v___x_3361_);
lean_ctor_set(v___x_3372_, 1, v___x_3359_);
lean_ctor_set(v___x_3372_, 2, v___x_3363_);
lean_ctor_set(v___x_3372_, 3, v___x_3366_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*4, v___x_3355_);
v___x_3373_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3371_, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3370_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
lean_ctor_set(v___x_3374_, 2, v_toProcessingContext_3337_);
lean_ctor_set(v___x_3374_, 3, v_fst_3349_);
lean_ctor_set(v___x_3374_, 4, v___x_3369_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3374_);
v___x_3376_ = v___x_3346_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
lean_del_object(v___x_3353_);
lean_dec(v_fst_3350_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___f_3340_);
lean_dec(v_old_x3f_3339_);
lean_dec_ref(v_setupImports_3338_);
v___x_3396_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3351_);
v___x_3397_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3398_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3399_ = lean_box(0);
v___x_3400_ = lean_unsigned_to_nat(32u);
v___x_3401_ = lean_mk_empty_array_with_capacity(v___x_3400_);
lean_dec_ref(v___x_3401_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3403_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3403_, 0, v___x_3397_);
lean_ctor_set(v___x_3403_, 1, v___x_3398_);
lean_ctor_set(v___x_3403_, 2, v___x_3399_);
lean_ctor_set(v___x_3403_, 3, v___x_3402_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*4, v___x_3355_);
lean_inc(v_fst_3349_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_fst_3349_);
v___x_3405_ = 0;
v___x_3406_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3406_, 0, v___x_3397_);
lean_ctor_set(v___x_3406_, 1, v___x_3396_);
lean_ctor_set(v___x_3406_, 2, v___x_3399_);
lean_ctor_set(v___x_3406_, 3, v___x_3402_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*4, v___x_3405_);
v___x_3407_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3404_, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3403_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
lean_ctor_set(v___x_3408_, 2, v_toProcessingContext_3337_);
lean_ctor_set(v___x_3408_, 3, v_fst_3349_);
lean_ctor_set(v___x_3408_, 4, v___x_3399_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3408_);
v___x_3410_ = v___x_3346_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___f_3340_);
lean_dec(v_old_x3f_3339_);
lean_dec_ref(v_setupImports_3338_);
lean_dec_ref(v_toProcessingContext_3337_);
v_a_3414_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3343_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3343_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3422_, lean_object* v_setupImports_3423_, lean_object* v_old_x3f_3424_, lean_object* v___f_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3422_, v_setupImports_3423_, v_old_x3f_3424_, v___f_3425_, v___y_3426_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3429_, lean_object* v_toProcessingContext_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3432_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3429_);
v___x_3433_ = lean_box(0);
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3435_, 0, v_x_3431_);
lean_ctor_set(v___x_3435_, 1, v___x_3432_);
lean_ctor_set(v___x_3435_, 2, v_toProcessingContext_3430_);
lean_ctor_set(v___x_3435_, 3, v___x_3433_);
lean_ctor_set(v___x_3435_, 4, v___x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3436_, lean_object* v_old_x3f_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_toProcessingContext_3440_; lean_object* v___x_3441_; lean_object* v___f_3442_; lean_object* v___f_3443_; lean_object* v___f_3444_; 
v_toProcessingContext_3440_ = lean_ctor_get(v_a_3438_, 0);
v___x_3441_ = l_Lean_Language_instInhabitedSnapshot_default;
lean_inc_ref(v_a_3438_);
lean_inc_ref(v_toProcessingContext_3440_);
v___f_3442_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3442_, 0, v_toProcessingContext_3440_);
lean_closure_set(v___f_3442_, 1, v_a_3438_);
lean_inc(v_old_x3f_3437_);
lean_inc_ref(v_toProcessingContext_3440_);
v___f_3443_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3443_, 0, v_toProcessingContext_3440_);
lean_closure_set(v___f_3443_, 1, v_setupImports_3436_);
lean_closure_set(v___f_3443_, 2, v_old_x3f_3437_);
lean_closure_set(v___f_3443_, 3, v___f_3442_);
lean_inc_ref(v_toProcessingContext_3440_);
v___f_3444_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3444_, 0, v___x_3441_);
lean_closure_set(v___f_3444_, 1, v_toProcessingContext_3440_);
if (lean_obj_tag(v_old_x3f_3437_) == 1)
{
lean_object* v_val_3445_; lean_object* v_result_x3f_3446_; 
v_val_3445_ = lean_ctor_get(v_old_x3f_3437_, 0);
lean_inc(v_val_3445_);
lean_dec_ref(v_old_x3f_3437_);
v_result_x3f_3446_ = lean_ctor_get(v_val_3445_, 4);
if (lean_obj_tag(v_result_x3f_3446_) == 1)
{
lean_object* v_stx_3447_; lean_object* v_val_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_stx_3447_ = lean_ctor_get(v_val_3445_, 3);
lean_inc(v_stx_3447_);
v_val_3448_ = lean_ctor_get(v_result_x3f_3446_, 0);
lean_inc(v_val_3445_);
v___x_3449_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3445_);
v___x_3450_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3449_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_val_3451_; 
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref(v___x_3450_);
if (lean_obj_tag(v_val_3451_) == 1)
{
lean_object* v_val_3452_; lean_object* v_firstCmdSnap_3453_; lean_object* v___x_3454_; 
v_val_3452_ = lean_ctor_get(v_val_3451_, 0);
lean_inc(v_val_3452_);
lean_dec_ref(v_val_3451_);
v_firstCmdSnap_3453_ = lean_ctor_get(v_val_3452_, 1);
lean_inc_ref(v_firstCmdSnap_3453_);
lean_dec(v_val_3452_);
v___x_3454_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3453_);
if (lean_obj_tag(v___x_3454_) == 1)
{
lean_object* v_val_3455_; lean_object* v_nextCmdSnap_x3f_3456_; 
v_val_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref(v___x_3454_);
v_nextCmdSnap_x3f_3456_ = lean_ctor_get(v_val_3455_, 4);
lean_inc(v_nextCmdSnap_x3f_3456_);
lean_dec(v_val_3455_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3456_) == 0)
{
lean_object* v___x_3457_; 
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3457_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3457_;
}
else
{
lean_object* v_val_3458_; lean_object* v___x_3459_; 
v_val_3458_ = lean_ctor_get(v_nextCmdSnap_x3f_3456_, 0);
lean_inc(v_val_3458_);
lean_dec_ref(v_nextCmdSnap_x3f_3456_);
v___x_3459_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3458_);
if (lean_obj_tag(v___x_3459_) == 1)
{
lean_object* v_val_3460_; lean_object* v_parserState_3461_; lean_object* v_pos_3462_; uint8_t v___x_3463_; 
v_val_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_val_3460_);
lean_dec_ref(v___x_3459_);
v_parserState_3461_ = lean_ctor_get(v_val_3460_, 2);
lean_inc_ref(v_parserState_3461_);
lean_dec(v_val_3460_);
v_pos_3462_ = lean_ctor_get(v_parserState_3461_, 0);
lean_inc(v_pos_3462_);
lean_dec_ref(v_parserState_3461_);
v___x_3463_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3462_, v_a_3438_);
lean_dec(v_pos_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3464_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3464_;
}
else
{
lean_object* v_parserState_3465_; lean_object* v___x_3466_; 
lean_inc_ref(v_toProcessingContext_3440_);
lean_dec_ref(v___f_3444_);
lean_dec_ref(v___f_3443_);
v_parserState_3465_ = lean_ctor_get(v_val_3448_, 0);
lean_inc_ref(v_parserState_3465_);
lean_inc_ref(v_a_3438_);
v___x_3466_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3440_, v_a_3438_, v_val_3445_, v_stx_3447_, v_parserState_3465_, v_a_3438_);
lean_dec_ref(v_a_3438_);
return v___x_3466_;
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v___x_3459_);
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3467_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3467_;
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec(v___x_3454_);
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3468_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3468_;
}
}
else
{
lean_object* v___x_3469_; 
lean_dec(v_val_3451_);
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3469_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3469_;
}
}
else
{
lean_object* v___x_3470_; 
lean_dec(v___x_3450_);
lean_dec(v_stx_3447_);
lean_dec(v_val_3445_);
v___x_3470_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3470_;
}
}
else
{
lean_object* v___x_3471_; 
lean_dec(v_val_3445_);
v___x_3471_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3471_;
}
}
else
{
lean_object* v___x_3472_; 
lean_dec(v_old_x3f_3437_);
v___x_3472_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3444_, v___f_3443_, v_a_3438_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3473_, lean_object* v_old_x3f_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3473_, v_old_x3f_3474_, v_a_3475_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3478_, lean_object* v_old_x3f_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v___x_3482_; 
lean_inc(v_old_x3f_3479_);
v___x_3482_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3482_, 0, v_setupImports_3478_);
lean_closure_set(v___x_3482_, 1, v_old_x3f_3479_);
if (lean_obj_tag(v_old_x3f_3479_) == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_box(0);
v___x_3484_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3482_, v___x_3483_, v_a_3480_);
return v___x_3484_;
}
else
{
lean_object* v_val_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3494_; 
v_val_3485_ = lean_ctor_get(v_old_x3f_3479_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_old_x3f_3479_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3487_ = v_old_x3f_3479_;
v_isShared_3488_ = v_isSharedCheck_3494_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_val_3485_);
lean_dec(v_old_x3f_3479_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3494_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_ictx_3489_; lean_object* v___x_3491_; 
v_ictx_3489_ = lean_ctor_get(v_val_3485_, 2);
lean_inc_ref(v_ictx_3489_);
lean_dec(v_val_3485_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_ictx_3489_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_ictx_3489_);
v___x_3491_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3482_, v___x_3491_, v_a_3480_);
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3495_, lean_object* v_old_x3f_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_Language_Lean_process(v_setupImports_3495_, v_old_x3f_3496_, v_a_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3500_, lean_object* v_parserState_3501_, lean_object* v_commandState_3502_, lean_object* v_old_x3f_3503_){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3513_; 
v___x_3505_ = lean_io_promise_new();
v___x_3506_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3503_) == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_box(0);
v___y_3513_ = v___x_3527_;
goto v___jp_3512_;
}
else
{
lean_object* v_val_3528_; lean_object* v_snd_3529_; lean_object* v___x_3530_; 
v_val_3528_ = lean_ctor_get(v_old_x3f_3503_, 0);
v_snd_3529_ = lean_ctor_get(v_val_3528_, 1);
lean_inc(v_snd_3529_);
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_snd_3529_);
v___y_3513_ = v___x_3530_;
goto v___jp_3512_;
}
v___jp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3508_, v___y_3509_, v_inputCtx_3500_);
lean_dec(v___x_3510_);
v___x_3511_ = l_IO_Promise_result_x21___redArg(v___x_3505_);
lean_dec(v___x_3505_);
return v___x_3511_;
}
v___jp_3512_:
{
uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = 1;
v___x_3515_ = lean_box(v___x_3514_);
lean_inc(v___x_3505_);
v___x_3516_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3516_, 0, v___y_3513_);
lean_closure_set(v___x_3516_, 1, v_parserState_3501_);
lean_closure_set(v___x_3516_, 2, v_commandState_3502_);
lean_closure_set(v___x_3516_, 3, v___x_3505_);
lean_closure_set(v___x_3516_, 4, v___x_3515_);
lean_closure_set(v___x_3516_, 5, v___x_3506_);
if (lean_obj_tag(v_old_x3f_3503_) == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_box(0);
v___y_3508_ = v___x_3516_;
v___y_3509_ = v___x_3517_;
goto v___jp_3507_;
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3526_; 
v_val_3518_ = lean_ctor_get(v_old_x3f_3503_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_old_x3f_3503_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3520_ = v_old_x3f_3503_;
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_val_3518_);
lean_dec(v_old_x3f_3503_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_fst_3522_; lean_object* v___x_3524_; 
v_fst_3522_ = lean_ctor_get(v_val_3518_, 0);
lean_inc(v_fst_3522_);
lean_dec(v_val_3518_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_fst_3522_);
v___x_3524_ = v___x_3520_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_fst_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
v___y_3508_ = v___x_3516_;
v___y_3509_ = v___x_3524_;
goto v___jp_3507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3531_, lean_object* v_parserState_3532_, lean_object* v_commandState_3533_, lean_object* v_old_x3f_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3531_, v_parserState_3532_, v_commandState_3533_, v_old_x3f_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3537_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3538_; 
v_nextCmdSnap_x3f_3538_ = lean_ctor_get(v_snap_3537_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3538_) == 1)
{
lean_object* v_val_3539_; lean_object* v___x_3540_; 
lean_inc_ref(v_nextCmdSnap_x3f_3538_);
lean_dec_ref(v_snap_3537_);
v_val_3539_ = lean_ctor_get(v_nextCmdSnap_x3f_3538_, 0);
lean_inc(v_val_3539_);
lean_dec_ref(v_nextCmdSnap_x3f_3538_);
v___x_3540_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3539_);
v_snap_3537_ = v___x_3540_;
goto _start;
}
else
{
lean_object* v_elabSnap_3542_; lean_object* v_resultSnap_3543_; lean_object* v___x_3544_; lean_object* v_cmdState_3545_; lean_object* v___x_3546_; 
v_elabSnap_3542_ = lean_ctor_get(v_snap_3537_, 3);
lean_inc_ref(v_elabSnap_3542_);
lean_dec_ref(v_snap_3537_);
v_resultSnap_3543_ = lean_ctor_get(v_elabSnap_3542_, 2);
lean_inc_ref(v_resultSnap_3543_);
lean_dec_ref(v_elabSnap_3542_);
v___x_3544_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3543_);
v_cmdState_3545_ = lean_ctor_get(v___x_3544_, 1);
lean_inc_ref(v_cmdState_3545_);
lean_dec(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_cmdState_3545_);
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3547_){
_start:
{
lean_object* v_result_x3f_3548_; 
v_result_x3f_3548_ = lean_ctor_get(v_snap_3547_, 4);
lean_inc(v_result_x3f_3548_);
lean_dec_ref(v_snap_3547_);
if (lean_obj_tag(v_result_x3f_3548_) == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_box(0);
return v___x_3549_;
}
else
{
lean_object* v_val_3550_; lean_object* v_processedSnap_3551_; lean_object* v___x_3552_; lean_object* v_result_x3f_3553_; 
v_val_3550_ = lean_ctor_get(v_result_x3f_3548_, 0);
lean_inc(v_val_3550_);
lean_dec_ref(v_result_x3f_3548_);
v_processedSnap_3551_ = lean_ctor_get(v_val_3550_, 1);
lean_inc_ref(v_processedSnap_3551_);
lean_dec(v_val_3550_);
v___x_3552_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3551_);
v_result_x3f_3553_ = lean_ctor_get(v___x_3552_, 2);
lean_inc(v_result_x3f_3553_);
lean_dec(v___x_3552_);
if (lean_obj_tag(v_result_x3f_3553_) == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_box(0);
return v___x_3554_;
}
else
{
lean_object* v_val_3555_; lean_object* v_firstCmdSnap_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_val_3555_ = lean_ctor_get(v_result_x3f_3553_, 0);
lean_inc(v_val_3555_);
lean_dec_ref(v_result_x3f_3553_);
v_firstCmdSnap_3556_ = lean_ctor_get(v_val_3555_, 1);
lean_inc_ref(v_firstCmdSnap_3556_);
lean_dec(v_val_3555_);
v___x_3557_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3556_);
v___x_3558_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3557_);
return v___x_3558_;
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

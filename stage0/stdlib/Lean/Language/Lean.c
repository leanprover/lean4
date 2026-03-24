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
lean_inc_ref(v_a_141_);
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
lean_inc(v_name_443_);
v___x_454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_454_, 0, v_name_443_);
lean_ctor_set(v___x_454_, 1, v_ref_445_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
lean_ctor_set(v___x_454_, 3, v_descr_448_);
lean_inc(v_name_443_);
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
static lean_object* _init_l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_492_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_493_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_494_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_495_ = l_Lean_Name_mkStr5(v___x_494_, v___x_493_, v___x_494_, v___x_492_, v___x_491_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_498_ = ((lean_object*)(l_Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_499_ = lean_obj_once(&l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_, &l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__once, _init_l_Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_);
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
lean_ctor_set(v___x_692_, 1, v___y_662_);
v___x_693_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_693_, 0, v___y_661_);
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
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
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
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
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
lean_inc_ref(v_fileName_727_);
v_fileMap_728_ = lean_ctor_get(v___y_655_, 1);
lean_inc_ref(v_fileMap_728_);
v_suppressElabErrors_729_ = lean_ctor_get_uint8(v___y_655_, sizeof(void*)*10);
lean_dec_ref(v___y_655_);
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
lean_inc_ref(v_fileMap_728_);
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
v___y_661_ = v_fileName_727_;
v___y_662_ = v_a_732_;
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
lean_dec_ref(v_fileName_727_);
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
v___y_661_ = v_fileName_727_;
v___y_662_ = v_a_732_;
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
lean_dec_ref(v___y_655_);
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
lean_dec_ref(v___y_655_);
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
lean_inc_ref(v___y_808_);
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
lean_inc_ref(v___y_845_);
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
v___x_974_ = lean_panic_fn(v___x_973_, v_msg_972_);
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
lean_inc_ref(v_fileName_1080_);
v_fileMap_1081_ = lean_ctor_get(v_toProcessingContext_1079_, 2);
lean_inc_ref(v_fileMap_1081_);
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
lean_dec_ref(v_a_1057_);
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
v___x_1133_ = l_Lean_FileMap_toPosition(v_fileMap_1081_, v_beginPos_1054_);
lean_dec(v_beginPos_1054_);
v___x_1134_ = 0;
v___x_1135_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_fst_1128_);
v___x_1137_ = l_Lean_MessageData_ofFormat(v___x_1136_);
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
lean_dec_ref(v_fileMap_1081_);
lean_dec_ref(v_fileName_1080_);
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
lean_inc_ref(v_toProcessingContext_1223_);
lean_dec_ref(v_a_1219_);
v___x_1224_ = l_Lean_MessageLog_empty;
v___x_1225_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1223_, v___x_1220_, v_parserState_1221_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, uint8_t v_val_1229_, lean_object* v_as_1230_, size_t v_sz_1231_, size_t v_i_1232_, lean_object* v_b_1233_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1232_, v_sz_1231_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v___x_1228_);
lean_dec_ref(v___x_1226_);
return v_b_1233_;
}
else
{
lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1254_; 
v_snd_1236_ = lean_ctor_get(v_b_1233_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_b_1233_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_b_1233_, 0);
lean_dec(v_unused_1255_);
v___x_1238_ = v_b_1233_;
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_dec(v_b_1233_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_a_1240_; lean_object* v_msg_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_a_1240_ = lean_array_uget_borrowed(v_as_1230_, v_i_1232_);
v_msg_1241_ = lean_ctor_get(v_a_1240_, 1);
v___x_1242_ = lean_box(0);
lean_inc_ref(v___x_1226_);
v___x_1243_ = l_Lean_FileMap_toPosition(v___x_1226_, v___x_1227_);
v___x_1244_ = 0;
v___x_1245_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1241_);
lean_inc_ref(v___x_1228_);
v___x_1246_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1246_, 0, v___x_1228_);
lean_ctor_set(v___x_1246_, 1, v___x_1243_);
lean_ctor_set(v___x_1246_, 2, v___x_1242_);
lean_ctor_set(v___x_1246_, 3, v___x_1245_);
lean_ctor_set(v___x_1246_, 4, v_msg_1241_);
lean_ctor_set_uint8(v___x_1246_, sizeof(void*)*5, v_val_1229_);
lean_ctor_set_uint8(v___x_1246_, sizeof(void*)*5 + 1, v___x_1244_);
lean_ctor_set_uint8(v___x_1246_, sizeof(void*)*5 + 2, v_val_1229_);
v___x_1247_ = l_Lean_MessageLog_add(v___x_1246_, v_snd_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1247_);
lean_ctor_set(v___x_1238_, 0, v___x_1242_);
v___x_1249_ = v___x_1238_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
size_t v___x_1250_; size_t v___x_1251_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1232_, v___x_1250_);
v_i_1232_ = v___x_1251_;
v_b_1233_ = v___x_1249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v_val_1259_, lean_object* v_as_1260_, lean_object* v_sz_1261_, lean_object* v_i_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_val_44554__boxed_1265_; size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_val_44554__boxed_1265_ = lean_unbox(v_val_1259_);
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1261_);
lean_dec(v_sz_1261_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1256_, v___x_1257_, v___x_1258_, v_val_44554__boxed_1265_, v_as_1260_, v_sz_boxed_1266_, v_i_boxed_1267_, v_b_1263_);
lean_dec_ref(v_as_1260_);
lean_dec(v___x_1257_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object* v___x_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, uint8_t v_val_1272_, lean_object* v_as_1273_, size_t v_sz_1274_, size_t v_i_1275_, lean_object* v_b_1276_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_usize_dec_lt(v_i_1275_, v_sz_1274_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1269_);
return v_b_1276_;
}
else
{
lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1297_; 
v_snd_1279_ = lean_ctor_get(v_b_1276_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_b_1276_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_b_1276_, 0);
lean_dec(v_unused_1298_);
v___x_1281_ = v_b_1276_;
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_dec(v_b_1276_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_a_1283_; lean_object* v_msg_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_a_1283_ = lean_array_uget_borrowed(v_as_1273_, v_i_1275_);
v_msg_1284_ = lean_ctor_get(v_a_1283_, 1);
v___x_1285_ = lean_box(0);
lean_inc_ref(v___x_1269_);
v___x_1286_ = l_Lean_FileMap_toPosition(v___x_1269_, v___x_1270_);
v___x_1287_ = 0;
v___x_1288_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1284_);
lean_inc_ref(v___x_1271_);
v___x_1289_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1289_, 0, v___x_1271_);
lean_ctor_set(v___x_1289_, 1, v___x_1286_);
lean_ctor_set(v___x_1289_, 2, v___x_1285_);
lean_ctor_set(v___x_1289_, 3, v___x_1288_);
lean_ctor_set(v___x_1289_, 4, v_msg_1284_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*5, v_val_1272_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*5 + 1, v___x_1287_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*5 + 2, v_val_1272_);
v___x_1290_ = l_Lean_MessageLog_add(v___x_1289_, v_snd_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1290_);
lean_ctor_set(v___x_1281_, 0, v___x_1285_);
v___x_1292_ = v___x_1281_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1275_, v___x_1293_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1269_, v___x_1270_, v___x_1271_, v_val_1272_, v_as_1273_, v_sz_1274_, v___x_1294_, v___x_1292_);
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object* v___x_1299_, lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v_val_1302_, lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_val_44606__boxed_1308_; size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_val_44606__boxed_1308_ = lean_unbox(v_val_1302_);
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1299_, v___x_1300_, v___x_1301_, v_val_44606__boxed_1308_, v_as_1303_, v_sz_boxed_1309_, v_i_boxed_1310_, v_b_1306_);
lean_dec_ref(v_as_1303_);
lean_dec(v___x_1300_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v___x_1314_, uint8_t v_val_1315_, lean_object* v_inh_1316_, lean_object* v_n_1317_, lean_object* v_b_1318_){
_start:
{
if (lean_obj_tag(v_n_1317_) == 0)
{
lean_object* v_cs_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1335_; 
v_cs_1320_ = lean_ctor_get(v_n_1317_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_n_1317_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1322_ = v_n_1317_;
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_cs_1320_);
lean_dec(v_n_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; size_t v_sz_1326_; size_t v___x_1327_; lean_object* v___x_1328_; lean_object* v_fst_1329_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v_b_1318_);
v_sz_1326_ = lean_array_size(v_cs_1320_);
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v___x_1312_, v___x_1313_, v___x_1314_, v_val_1315_, v_inh_1316_, v_cs_1320_, v_sz_1326_, v___x_1327_, v___x_1325_);
lean_dec_ref(v_cs_1320_);
v_fst_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_fst_1329_);
if (lean_obj_tag(v_fst_1329_) == 0)
{
lean_object* v_snd_1330_; lean_object* v___x_1332_; 
v_snd_1330_ = lean_ctor_get(v___x_1328_, 1);
lean_inc(v_snd_1330_);
lean_dec_ref(v___x_1328_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 1);
lean_ctor_set(v___x_1322_, 0, v_snd_1330_);
v___x_1332_ = v___x_1322_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_snd_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v_val_1334_; 
lean_dec_ref(v___x_1328_);
lean_del_object(v___x_1322_);
v_val_1334_ = lean_ctor_get(v_fst_1329_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v_fst_1329_);
return v_val_1334_;
}
}
}
else
{
lean_object* v_vs_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1351_; 
v_vs_1336_ = lean_ctor_get(v_n_1317_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_n_1317_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1338_ = v_n_1317_;
v_isShared_1339_ = v_isSharedCheck_1351_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_vs_1336_);
lean_dec(v_n_1317_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1351_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; size_t v_sz_1342_; size_t v___x_1343_; lean_object* v___x_1344_; lean_object* v_fst_1345_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_b_1318_);
v_sz_1342_ = lean_array_size(v_vs_1336_);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1312_, v___x_1313_, v___x_1314_, v_val_1315_, v_vs_1336_, v_sz_1342_, v___x_1343_, v___x_1341_);
lean_dec_ref(v_vs_1336_);
v_fst_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1345_);
if (lean_obj_tag(v_fst_1345_) == 0)
{
lean_object* v_snd_1346_; lean_object* v___x_1348_; 
v_snd_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec_ref(v___x_1344_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_snd_1346_);
v___x_1348_ = v___x_1338_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_snd_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v_val_1350_; 
lean_dec_ref(v___x_1344_);
lean_del_object(v___x_1338_);
v_val_1350_ = lean_ctor_get(v_fst_1345_, 0);
lean_inc(v_val_1350_);
lean_dec_ref(v_fst_1345_);
return v_val_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, uint8_t v_val_1355_, lean_object* v_inh_1356_, lean_object* v_as_1357_, size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_b_1360_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_usize_dec_lt(v_i_1359_, v_sz_1358_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1352_);
return v_b_1360_;
}
else
{
lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1381_; 
v_snd_1363_ = lean_ctor_get(v_b_1360_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_b_1360_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_b_1360_, 0);
lean_dec(v_unused_1382_);
v___x_1365_ = v_b_1360_;
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_b_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_array_uget_borrowed(v_as_1357_, v_i_1359_);
lean_inc(v_snd_1363_);
lean_inc(v_a_1367_);
lean_inc_ref(v___x_1354_);
lean_inc_ref(v___x_1352_);
v___x_1368_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1352_, v___x_1353_, v___x_1354_, v_val_1355_, v_inh_1356_, v_a_1367_, v_snd_1363_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1352_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1363_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec(v_snd_1363_);
v_a_1373_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1368_);
v___x_1374_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_a_1373_);
lean_ctor_set(v___x_1365_, 0, v___x_1374_);
v___x_1376_ = v___x_1365_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_a_1373_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
size_t v___x_1377_; size_t v___x_1378_; 
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1359_, v___x_1377_);
v_i_1359_ = v___x_1378_;
v_b_1360_ = v___x_1376_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v___x_1385_, lean_object* v_val_1386_, lean_object* v_inh_1387_, lean_object* v_as_1388_, lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_val_44657__boxed_1393_; size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_val_44657__boxed_1393_ = lean_unbox(v_val_1386_);
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v___x_1383_, v___x_1384_, v___x_1385_, v_val_44657__boxed_1393_, v_inh_1387_, v_as_1388_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1391_);
lean_dec_ref(v_as_1388_);
lean_dec_ref(v_inh_1387_);
lean_dec(v___x_1384_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_val_1400_, lean_object* v_inh_1401_, lean_object* v_n_1402_, lean_object* v_b_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v_val_44673__boxed_1405_; lean_object* v_res_1406_; 
v_val_44673__boxed_1405_ = lean_unbox(v_val_1400_);
v_res_1406_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1397_, v___x_1398_, v___x_1399_, v_val_44673__boxed_1405_, v_inh_1401_, v_n_1402_, v_b_1403_);
lean_dec_ref(v_inh_1401_);
lean_dec(v___x_1398_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, uint8_t v_val_1410_, lean_object* v_as_1411_, size_t v_sz_1412_, size_t v_i_1413_, lean_object* v_b_1414_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_lt(v_i_1413_, v_sz_1412_);
if (v___x_1416_ == 0)
{
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___x_1407_);
return v_b_1414_;
}
else
{
lean_object* v_snd_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1435_; 
v_snd_1417_ = lean_ctor_get(v_b_1414_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_b_1414_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_b_1414_, 0);
lean_dec(v_unused_1436_);
v___x_1419_ = v_b_1414_;
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_snd_1417_);
lean_dec(v_b_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_a_1421_; lean_object* v_msg_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v_a_1421_ = lean_array_uget_borrowed(v_as_1411_, v_i_1413_);
v_msg_1422_ = lean_ctor_get(v_a_1421_, 1);
v___x_1423_ = lean_box(0);
lean_inc_ref(v___x_1407_);
v___x_1424_ = l_Lean_FileMap_toPosition(v___x_1407_, v___x_1408_);
v___x_1425_ = 0;
v___x_1426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1422_);
lean_inc_ref(v___x_1409_);
v___x_1427_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1427_, 0, v___x_1409_);
lean_ctor_set(v___x_1427_, 1, v___x_1424_);
lean_ctor_set(v___x_1427_, 2, v___x_1423_);
lean_ctor_set(v___x_1427_, 3, v___x_1426_);
lean_ctor_set(v___x_1427_, 4, v_msg_1422_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*5, v_val_1410_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*5 + 1, v___x_1425_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*5 + 2, v_val_1410_);
v___x_1428_ = l_Lean_MessageLog_add(v___x_1427_, v_snd_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v___x_1428_);
lean_ctor_set(v___x_1419_, 0, v___x_1423_);
v___x_1430_ = v___x_1419_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1413_, v___x_1431_);
v_i_1413_ = v___x_1432_;
v_b_1414_ = v___x_1430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1437_, lean_object* v___x_1438_, lean_object* v___x_1439_, lean_object* v_val_1440_, lean_object* v_as_1441_, lean_object* v_sz_1442_, lean_object* v_i_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_val_44779__boxed_1446_; size_t v_sz_boxed_1447_; size_t v_i_boxed_1448_; lean_object* v_res_1449_; 
v_val_44779__boxed_1446_ = lean_unbox(v_val_1440_);
v_sz_boxed_1447_ = lean_unbox_usize(v_sz_1442_);
lean_dec(v_sz_1442_);
v_i_boxed_1448_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1437_, v___x_1438_, v___x_1439_, v_val_44779__boxed_1446_, v_as_1441_, v_sz_boxed_1447_, v_i_boxed_1448_, v_b_1444_);
lean_dec_ref(v_as_1441_);
lean_dec(v___x_1438_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, uint8_t v_val_1453_, lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1459_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___x_1450_);
return v_b_1457_;
}
else
{
lean_object* v_snd_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1478_; 
v_snd_1460_ = lean_ctor_get(v_b_1457_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_b_1457_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_b_1457_, 0);
lean_dec(v_unused_1479_);
v___x_1462_ = v_b_1457_;
v_isShared_1463_ = v_isSharedCheck_1478_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_snd_1460_);
lean_dec(v_b_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1478_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_a_1464_; lean_object* v_msg_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v_a_1464_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
v_msg_1465_ = lean_ctor_get(v_a_1464_, 1);
v___x_1466_ = lean_box(0);
lean_inc_ref(v___x_1450_);
v___x_1467_ = l_Lean_FileMap_toPosition(v___x_1450_, v___x_1451_);
v___x_1468_ = 0;
v___x_1469_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1465_);
lean_inc_ref(v___x_1452_);
v___x_1470_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1470_, 0, v___x_1452_);
lean_ctor_set(v___x_1470_, 1, v___x_1467_);
lean_ctor_set(v___x_1470_, 2, v___x_1466_);
lean_ctor_set(v___x_1470_, 3, v___x_1469_);
lean_ctor_set(v___x_1470_, 4, v_msg_1465_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*5, v_val_1453_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*5 + 1, v___x_1468_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*5 + 2, v_val_1453_);
v___x_1471_ = l_Lean_MessageLog_add(v___x_1470_, v_snd_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 1, v___x_1471_);
lean_ctor_set(v___x_1462_, 0, v___x_1466_);
v___x_1473_ = v___x_1462_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_add(v_i_1456_, v___x_1474_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1450_, v___x_1451_, v___x_1452_, v_val_1453_, v_as_1454_, v_sz_1455_, v___x_1475_, v___x_1473_);
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_val_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v_val_44831__boxed_1489_; size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_val_44831__boxed_1489_ = lean_unbox(v_val_1483_);
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1480_, v___x_1481_, v___x_1482_, v_val_44831__boxed_1489_, v_as_1484_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1487_);
lean_dec_ref(v_as_1484_);
lean_dec(v___x_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1493_, lean_object* v___x_1494_, lean_object* v___x_1495_, uint8_t v_val_1496_, lean_object* v_t_1497_, lean_object* v_init_1498_){
_start:
{
lean_object* v_root_1500_; lean_object* v_tail_1501_; lean_object* v___x_1502_; 
v_root_1500_ = lean_ctor_get(v_t_1497_, 0);
lean_inc_ref(v_root_1500_);
v_tail_1501_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_tail_1501_);
lean_dec_ref(v_t_1497_);
lean_inc_ref(v_init_1498_);
lean_inc_ref(v___x_1495_);
lean_inc_ref(v___x_1493_);
v___x_1502_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v___x_1493_, v___x_1494_, v___x_1495_, v_val_1496_, v_init_1498_, v_root_1500_, v_init_1498_);
lean_dec_ref(v_init_1498_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; 
lean_dec_ref(v_tail_1501_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v___x_1493_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
return v_a_1503_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; lean_object* v_fst_1510_; 
v_a_1504_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1502_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_a_1504_);
v_sz_1507_ = lean_array_size(v_tail_1501_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1493_, v___x_1494_, v___x_1495_, v_val_1496_, v_tail_1501_, v_sz_1507_, v___x_1508_, v___x_1506_);
lean_dec_ref(v_tail_1501_);
v_fst_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_fst_1510_);
if (lean_obj_tag(v_fst_1510_) == 0)
{
lean_object* v_snd_1511_; 
v_snd_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_snd_1511_);
lean_dec_ref(v___x_1509_);
return v_snd_1511_;
}
else
{
lean_object* v_val_1512_; 
lean_dec_ref(v___x_1509_);
v_val_1512_ = lean_ctor_get(v_fst_1510_, 0);
lean_inc(v_val_1512_);
lean_dec_ref(v_fst_1510_);
return v_val_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v_val_1516_, lean_object* v_t_1517_, lean_object* v_init_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_val_44882__boxed_1520_; lean_object* v_res_1521_; 
v_val_44882__boxed_1520_ = lean_unbox(v_val_1516_);
v_res_1521_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1513_, v___x_1514_, v___x_1515_, v_val_44882__boxed_1520_, v_t_1517_, v_init_1518_);
lean_dec(v___x_1514_);
return v_res_1521_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = l_Lean_firstFrontendMacroScope;
v___x_1524_ = lean_nat_add(v___x_1523_, v___x_1522_);
return v___x_1524_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1531_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v___x_1538_, size_t v___x_1539_, uint8_t v___x_1540_, lean_object* v_env_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v_a_1544_, lean_object* v_opts_1545_, lean_object* v___x_1546_, lean_object* v_pos_1547_, uint8_t v_val_1548_, lean_object* v___x_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v___x_1552_, uint8_t v___x_1553_, lean_object* v_x_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_toProcessingContext_1575_; lean_object* v_fileName_1576_; lean_object* v_fileMap_1577_; lean_object* v_env_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v_fileName_1584_; lean_object* v_fileMap_1585_; lean_object* v_currRecDepth_1586_; lean_object* v_ref_1587_; lean_object* v_currNamespace_1588_; lean_object* v_openDecls_1589_; lean_object* v_initHeartbeats_1590_; lean_object* v_maxHeartbeats_1591_; lean_object* v_quotContext_1592_; lean_object* v_currMacroScope_1593_; lean_object* v_cancelTk_x3f_1594_; uint8_t v_suppressElabErrors_1595_; lean_object* v_inheritedTraceOptions_1596_; lean_object* v___y_1597_; uint8_t v___y_1614_; uint8_t v___x_1634_; 
v___x_1556_ = l_Lean_firstFrontendMacroScope;
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1559_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1560_ = lean_box(0);
lean_inc(v___x_1536_);
v___x_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1536_);
lean_ctor_set(v___x_1561_, 1, v___x_1557_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
v___x_1562_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1563_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1537_);
lean_inc_ref(v___x_1564_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_inc_n(v___x_1538_, 2);
v___x_1566_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1564_);
lean_ctor_set(v___x_1566_, 2, v___x_1538_);
lean_ctor_set(v___x_1566_, 3, v___x_1538_);
lean_ctor_set_usize(v___x_1566_, 4, v___x_1539_);
v___x_1567_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1566_, 2);
v___x_1568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1569_, 0, v___x_1562_);
lean_ctor_set(v___x_1569_, 1, v___x_1562_);
lean_ctor_set(v___x_1569_, 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*3, v___x_1540_);
v___x_1570_ = lean_mk_empty_array_with_capacity(v___x_1538_);
lean_inc_ref(v___x_1570_);
lean_inc_ref(v___x_1542_);
v___x_1571_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1571_, 0, v_env_1541_);
lean_ctor_set(v___x_1571_, 1, v___x_1558_);
lean_ctor_set(v___x_1571_, 2, v___x_1559_);
lean_ctor_set(v___x_1571_, 3, v___x_1561_);
lean_ctor_set(v___x_1571_, 4, v___x_1542_);
lean_ctor_set(v___x_1571_, 5, v___x_1563_);
lean_ctor_set(v___x_1571_, 6, v___x_1568_);
lean_ctor_set(v___x_1571_, 7, v___x_1569_);
lean_ctor_set(v___x_1571_, 8, v___x_1570_);
v___x_1572_ = lean_st_mk_ref(v___x_1571_);
v___x_1573_ = lean_st_ref_get(v___x_1543_);
v___x_1574_ = lean_st_ref_get(v___x_1572_);
v_toProcessingContext_1575_ = lean_ctor_get(v_a_1544_, 0);
lean_inc_ref(v_toProcessingContext_1575_);
lean_dec_ref(v_a_1544_);
v_fileName_1576_ = lean_ctor_get(v_toProcessingContext_1575_, 1);
lean_inc_ref(v_fileName_1576_);
v_fileMap_1577_ = lean_ctor_get(v_toProcessingContext_1575_, 2);
lean_inc_ref(v_fileMap_1577_);
lean_dec_ref(v_toProcessingContext_1575_);
v_env_1578_ = lean_ctor_get(v___x_1574_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1574_);
v___x_1579_ = lean_box(0);
v___x_1580_ = l_Lean_Core_getMaxHeartbeats(v_opts_1545_);
v___x_1581_ = l_Lean_diagnostics;
v___x_1582_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1545_, v___x_1581_);
v___x_1634_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1578_);
lean_dec_ref(v_env_1578_);
if (v___x_1634_ == 0)
{
if (v___x_1582_ == 0)
{
v___y_1614_ = v___x_1553_;
goto v___jp_1613_;
}
else
{
v___y_1614_ = v___x_1634_;
goto v___jp_1613_;
}
}
else
{
v___y_1614_ = v___x_1582_;
goto v___jp_1613_;
}
v___jp_1583_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = l_Lean_maxRecDepth;
v___x_1599_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1545_, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1600_, 0, v_fileName_1584_);
lean_ctor_set(v___x_1600_, 1, v_fileMap_1585_);
lean_ctor_set(v___x_1600_, 2, v_opts_1545_);
lean_ctor_set(v___x_1600_, 3, v_currRecDepth_1586_);
lean_ctor_set(v___x_1600_, 4, v___x_1599_);
lean_ctor_set(v___x_1600_, 5, v_ref_1587_);
lean_ctor_set(v___x_1600_, 6, v_currNamespace_1588_);
lean_ctor_set(v___x_1600_, 7, v_openDecls_1589_);
lean_ctor_set(v___x_1600_, 8, v_initHeartbeats_1590_);
lean_ctor_set(v___x_1600_, 9, v_maxHeartbeats_1591_);
lean_ctor_set(v___x_1600_, 10, v_quotContext_1592_);
lean_ctor_set(v___x_1600_, 11, v_currMacroScope_1593_);
lean_ctor_set(v___x_1600_, 12, v_cancelTk_x3f_1594_);
lean_ctor_set(v___x_1600_, 13, v_inheritedTraceOptions_1596_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*14, v___x_1582_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*14 + 1, v_suppressElabErrors_1595_);
v___x_1601_ = l_Lean_Language_SnapshotTree_trace(v___x_1546_, v___x_1600_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v_traceState_1603_; lean_object* v_traces_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v___x_1601_);
lean_dec_ref(v___x_1551_);
v___x_1602_ = lean_st_ref_get(v___x_1572_);
lean_dec(v___x_1572_);
v_traceState_1603_ = lean_ctor_get(v___x_1602_, 4);
lean_inc_ref(v_traceState_1603_);
lean_dec(v___x_1602_);
v_traces_1604_ = lean_ctor_get(v_traceState_1603_, 0);
lean_inc_ref(v_traces_1604_);
lean_dec_ref(v_traceState_1603_);
v___x_1605_ = l_Lean_MessageLog_empty;
v___x_1606_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1577_, v_pos_1547_, v_fileName_1576_, v_val_1548_, v_traces_1604_, v___x_1605_);
v___x_1607_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1608_, 0, v___x_1549_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
lean_ctor_set(v___x_1608_, 2, v___x_1550_);
lean_ctor_set(v___x_1608_, 3, v___x_1542_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*4, v_val_1548_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1570_);
v___x_1610_ = lean_task_pure(v___x_1609_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v___x_1601_);
lean_dec_ref(v_fileMap_1577_);
lean_dec_ref(v_fileName_1576_);
lean_dec(v___x_1572_);
lean_dec(v___x_1550_);
lean_dec_ref(v___x_1549_);
lean_dec_ref(v___x_1542_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1551_);
lean_ctor_set(v___x_1611_, 1, v___x_1570_);
v___x_1612_ = lean_task_pure(v___x_1611_);
return v___x_1612_;
}
}
v___jp_1613_:
{
if (v___y_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v_env_1616_; lean_object* v_nextMacroScope_1617_; lean_object* v_ngen_1618_; lean_object* v_auxDeclNGen_1619_; lean_object* v_traceState_1620_; lean_object* v_messages_1621_; lean_object* v_infoState_1622_; lean_object* v_snapshotTasks_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1632_; 
v___x_1615_ = lean_st_ref_take(v___x_1572_);
v_env_1616_ = lean_ctor_get(v___x_1615_, 0);
v_nextMacroScope_1617_ = lean_ctor_get(v___x_1615_, 1);
v_ngen_1618_ = lean_ctor_get(v___x_1615_, 2);
v_auxDeclNGen_1619_ = lean_ctor_get(v___x_1615_, 3);
v_traceState_1620_ = lean_ctor_get(v___x_1615_, 4);
v_messages_1621_ = lean_ctor_get(v___x_1615_, 6);
v_infoState_1622_ = lean_ctor_get(v___x_1615_, 7);
v_snapshotTasks_1623_ = lean_ctor_get(v___x_1615_, 8);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v___x_1615_, 5);
lean_dec(v_unused_1633_);
v___x_1625_ = v___x_1615_;
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snapshotTasks_1623_);
lean_inc(v_infoState_1622_);
lean_inc(v_messages_1621_);
lean_inc(v_traceState_1620_);
lean_inc(v_auxDeclNGen_1619_);
lean_inc(v_ngen_1618_);
lean_inc(v_nextMacroScope_1617_);
lean_inc(v_env_1616_);
lean_dec(v___x_1615_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = l_Lean_Kernel_enableDiag(v_env_1616_, v___x_1582_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 5, v___x_1563_);
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_nextMacroScope_1617_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_ngen_1618_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_auxDeclNGen_1619_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_traceState_1620_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_messages_1621_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v_infoState_1622_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_snapshotTasks_1623_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_st_ref_set(v___x_1572_, v___x_1629_);
lean_inc(v___x_1572_);
lean_inc(v___x_1536_);
lean_inc(v___x_1538_);
lean_inc_ref(v_fileMap_1577_);
lean_inc_ref(v_fileName_1576_);
v_fileName_1584_ = v_fileName_1576_;
v_fileMap_1585_ = v_fileMap_1577_;
v_currRecDepth_1586_ = v___x_1538_;
v_ref_1587_ = v___x_1579_;
v_currNamespace_1588_ = v___x_1536_;
v_openDecls_1589_ = v___x_1560_;
v_initHeartbeats_1590_ = v___x_1538_;
v_maxHeartbeats_1591_ = v___x_1580_;
v_quotContext_1592_ = v___x_1536_;
v_currMacroScope_1593_ = v___x_1556_;
v_cancelTk_x3f_1594_ = v___x_1552_;
v_suppressElabErrors_1595_ = v_val_1548_;
v_inheritedTraceOptions_1596_ = v___x_1573_;
v___y_1597_ = v___x_1572_;
goto v___jp_1583_;
}
}
}
else
{
lean_inc(v___x_1572_);
lean_inc(v___x_1536_);
lean_inc(v___x_1538_);
lean_inc_ref(v_fileMap_1577_);
lean_inc_ref(v_fileName_1576_);
v_fileName_1584_ = v_fileName_1576_;
v_fileMap_1585_ = v_fileMap_1577_;
v_currRecDepth_1586_ = v___x_1538_;
v_ref_1587_ = v___x_1579_;
v_currNamespace_1588_ = v___x_1536_;
v_openDecls_1589_ = v___x_1560_;
v_initHeartbeats_1590_ = v___x_1538_;
v_maxHeartbeats_1591_ = v___x_1580_;
v_quotContext_1592_ = v___x_1536_;
v_currMacroScope_1593_ = v___x_1556_;
v_cancelTk_x3f_1594_ = v___x_1552_;
v_suppressElabErrors_1595_ = v_val_1548_;
v_inheritedTraceOptions_1596_ = v___x_1573_;
v___y_1597_ = v___x_1572_;
goto v___jp_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1635_ = _args[0];
lean_object* v___x_1636_ = _args[1];
lean_object* v___x_1637_ = _args[2];
lean_object* v___x_1638_ = _args[3];
lean_object* v___x_1639_ = _args[4];
lean_object* v_env_1640_ = _args[5];
lean_object* v___x_1641_ = _args[6];
lean_object* v___x_1642_ = _args[7];
lean_object* v_a_1643_ = _args[8];
lean_object* v_opts_1644_ = _args[9];
lean_object* v___x_1645_ = _args[10];
lean_object* v_pos_1646_ = _args[11];
lean_object* v_val_1647_ = _args[12];
lean_object* v___x_1648_ = _args[13];
lean_object* v___x_1649_ = _args[14];
lean_object* v___x_1650_ = _args[15];
lean_object* v___x_1651_ = _args[16];
lean_object* v___x_1652_ = _args[17];
lean_object* v_x_1653_ = _args[18];
lean_object* v___y_1654_ = _args[19];
_start:
{
size_t v___x_44943__boxed_1655_; uint8_t v___x_44944__boxed_1656_; uint8_t v_val_44948__boxed_1657_; uint8_t v___x_44953__boxed_1658_; lean_object* v_res_1659_; 
v___x_44943__boxed_1655_ = lean_unbox_usize(v___x_1638_);
lean_dec(v___x_1638_);
v___x_44944__boxed_1656_ = lean_unbox(v___x_1639_);
v_val_44948__boxed_1657_ = lean_unbox(v_val_1647_);
v___x_44953__boxed_1658_ = lean_unbox(v___x_1652_);
v_res_1659_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1635_, v___x_1636_, v___x_1637_, v___x_44943__boxed_1655_, v___x_44944__boxed_1656_, v_env_1640_, v___x_1641_, v___x_1642_, v_a_1643_, v_opts_1644_, v___x_1645_, v_pos_1646_, v_val_44948__boxed_1657_, v___x_1648_, v___x_1649_, v___x_1650_, v___x_1651_, v___x_44953__boxed_1658_, v_x_1653_);
lean_dec(v_pos_1646_);
lean_dec(v___x_1642_);
lean_dec(v___x_1636_);
return v_res_1659_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1666_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1667_ = l_Lean_Name_append(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1668_, lean_object* v___x_1669_, uint8_t v_val_1670_, lean_object* v_val_1671_, lean_object* v_val_1672_, lean_object* v___x_1673_, lean_object* v___x_1674_, uint8_t v___x_1675_, lean_object* v_a_1676_, lean_object* v_pos_1677_, lean_object* v_infoSt_1678_){
_start:
{
lean_object* v___y_1681_; lean_object* v_msgLog_1682_; lean_object* v___y_1688_; lean_object* v_trees_1720_; lean_object* v_size_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_trees_1720_ = lean_ctor_get(v_infoSt_1678_, 2);
lean_inc_ref(v_trees_1720_);
lean_dec_ref(v_infoSt_1678_);
v_size_1721_ = lean_ctor_get(v_trees_1720_, 2);
v___x_1722_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1723_ = lean_nat_dec_lt(v___x_1674_, v_size_1721_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec_ref(v_trees_1720_);
v___x_1724_ = l_outOfBounds___redArg(v___x_1722_);
v___y_1688_ = v___x_1724_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1722_, v_trees_1720_, v___x_1674_);
v___y_1688_ = v___x_1725_;
goto v___jp_1687_;
}
v___jp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___y_1681_);
v___x_1685_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1668_);
lean_ctor_set(v___x_1685_, 1, v___x_1683_);
lean_ctor_set(v___x_1685_, 2, v___x_1684_);
lean_ctor_set(v___x_1685_, 3, v___x_1669_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*4, v_val_1670_);
v___x_1686_ = lean_io_promise_resolve(v___x_1685_, v_val_1671_);
return v___x_1686_;
}
v___jp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_scopes_1691_; lean_object* v___x_1692_; lean_object* v_opts_1693_; uint8_t v_hasTrace_1694_; lean_object* v___x_1695_; 
v___x_1689_ = l_Lean_inheritedTraceOptions;
v___x_1690_ = lean_st_ref_get(v___x_1689_);
v_scopes_1691_ = lean_ctor_get(v_val_1672_, 2);
v___x_1692_ = l_List_head_x21___redArg(v___x_1673_, v_scopes_1691_);
v_opts_1693_ = lean_ctor_get(v___x_1692_, 1);
lean_inc_ref(v_opts_1693_);
lean_dec(v___x_1692_);
v_hasTrace_1694_ = lean_ctor_get_uint8(v_opts_1693_, sizeof(void*)*1);
v___x_1695_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1694_ == 0)
{
lean_dec_ref(v_opts_1693_);
lean_dec(v___x_1690_);
lean_dec_ref(v_a_1676_);
lean_dec(v___x_1674_);
v___y_1681_ = v___y_1688_;
v_msgLog_1682_ = v___x_1695_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1696_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1697_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1698_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1690_, v_opts_1693_, v___x_1698_);
lean_dec_ref(v_opts_1693_);
lean_dec(v___x_1690_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_a_1676_);
lean_dec(v___x_1674_);
v___y_1681_ = v___y_1688_;
v_msgLog_1682_ = v___x_1695_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_box(0);
lean_inc_ref(v___y_1688_);
v___x_1701_ = l_Lean_Elab_InfoTree_format(v___y_1688_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; double v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_toProcessingContext_1706_; lean_object* v_fileName_1707_; lean_object* v_fileMap_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = lean_float_of_nat(v___x_1674_);
v___x_1704_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1705_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1705_, 0, v___x_1696_);
lean_ctor_set(v___x_1705_, 1, v___x_1700_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
lean_ctor_set_float(v___x_1705_, sizeof(void*)*3, v___x_1703_);
lean_ctor_set_float(v___x_1705_, sizeof(void*)*3 + 8, v___x_1703_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*3 + 16, v___x_1675_);
v_toProcessingContext_1706_ = lean_ctor_get(v_a_1676_, 0);
lean_inc_ref(v_toProcessingContext_1706_);
lean_dec_ref(v_a_1676_);
v_fileName_1707_ = lean_ctor_get(v_toProcessingContext_1706_, 1);
lean_inc_ref(v_fileName_1707_);
v_fileMap_1708_ = lean_ctor_get(v_toProcessingContext_1706_, 2);
lean_inc_ref(v_fileMap_1708_);
lean_dec_ref(v_toProcessingContext_1706_);
v___x_1709_ = l_Lean_MessageData_nil;
v___x_1710_ = l_Lean_MessageData_ofFormat(v_a_1702_);
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_mk_empty_array_with_capacity(v___x_1711_);
v___x_1713_ = lean_array_push(v___x_1712_, v___x_1710_);
v___x_1714_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1705_);
lean_ctor_set(v___x_1714_, 1, v___x_1709_);
lean_ctor_set(v___x_1714_, 2, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1697_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_FileMap_toPosition(v_fileMap_1708_, v_pos_1677_);
v___x_1717_ = 0;
v___x_1718_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1718_, 0, v_fileName_1707_);
lean_ctor_set(v___x_1718_, 1, v___x_1716_);
lean_ctor_set(v___x_1718_, 2, v___x_1700_);
lean_ctor_set(v___x_1718_, 3, v___x_1704_);
lean_ctor_set(v___x_1718_, 4, v___x_1715_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*5, v_val_1670_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*5 + 1, v___x_1717_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*5 + 2, v_val_1670_);
v___x_1719_ = l_Lean_MessageLog_add(v___x_1718_, v___x_1695_);
v___y_1681_ = v___y_1688_;
v_msgLog_1682_ = v___x_1719_;
goto v___jp_1680_;
}
else
{
lean_dec_ref(v___x_1701_);
lean_dec_ref(v_a_1676_);
lean_dec(v___x_1674_);
v___y_1681_ = v___y_1688_;
v_msgLog_1682_ = v___x_1695_;
goto v___jp_1680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_val_1728_, lean_object* v_val_1729_, lean_object* v_val_1730_, lean_object* v___x_1731_, lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v_a_1734_, lean_object* v_pos_1735_, lean_object* v_infoSt_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v_val_45130__boxed_1738_; uint8_t v___x_45135__boxed_1739_; lean_object* v_res_1740_; 
v_val_45130__boxed_1738_ = lean_unbox(v_val_1728_);
v___x_45135__boxed_1739_ = lean_unbox(v___x_1733_);
v_res_1740_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1726_, v___x_1727_, v_val_45130__boxed_1738_, v_val_1729_, v_val_1730_, v___x_1731_, v___x_1732_, v___x_45135__boxed_1739_, v_a_1734_, v_pos_1735_, v_infoSt_1736_);
lean_dec(v_pos_1735_);
lean_dec_ref(v_val_1730_);
lean_dec(v_val_1729_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1742_, size_t v_i_1743_, size_t v_stop_1744_, lean_object* v_b_1745_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_eq(v_i_1743_, v_stop_1744_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; size_t v___x_1751_; size_t v___x_1752_; 
v___x_1748_ = lean_array_uget_borrowed(v_as_1742_, v_i_1743_);
v___f_1749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1748_);
v___x_1750_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1749_, v___x_1748_);
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1743_, v___x_1751_);
v_i_1743_ = v___x_1752_;
v_b_1745_ = v___x_1750_;
goto _start;
}
else
{
return v_b_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1754_, lean_object* v_i_1755_, lean_object* v_stop_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_){
_start:
{
size_t v_i_boxed_1759_; size_t v_stop_boxed_1760_; lean_object* v_res_1761_; 
v_i_boxed_1759_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_stop_boxed_1760_ = lean_unbox_usize(v_stop_1756_);
lean_dec(v_stop_1756_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1754_, v_i_boxed_1759_, v_stop_boxed_1760_, v_b_1757_);
lean_dec_ref(v_as_1754_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1762_, lean_object* v_newParserState_1763_, lean_object* v_val_1764_, lean_object* v_sync_1765_, lean_object* v_val_1766_, lean_object* v_a_1767_, lean_object* v_oldNext_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v_sync_boxed_1770_; lean_object* v_res_1771_; 
v_sync_boxed_1770_ = lean_unbox(v_sync_1765_);
v_res_1771_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1762_, v_newParserState_1763_, v_val_1764_, v_sync_boxed_1770_, v_val_1766_, v_a_1767_, v_oldNext_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1772_, lean_object* v_newParserState_1773_, lean_object* v_val_1774_, uint8_t v_sync_1775_, lean_object* v_val_1776_, lean_object* v_a_1777_, lean_object* v_oldResult_1778_){
_start:
{
lean_object* v_task_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v_task_1780_ = lean_ctor_get(v_val_1772_, 3);
lean_inc_ref(v_task_1780_);
lean_dec_ref(v_val_1772_);
v___x_1781_ = lean_box(v_sync_1775_);
lean_inc_ref(v_a_1777_);
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1782_, 0, v_oldResult_1778_);
lean_closure_set(v___f_1782_, 1, v_newParserState_1773_);
lean_closure_set(v___f_1782_, 2, v_val_1774_);
lean_closure_set(v___f_1782_, 3, v___x_1781_);
lean_closure_set(v___f_1782_, 4, v_val_1776_);
lean_closure_set(v___f_1782_, 5, v_a_1777_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = 1;
v___x_1785_ = l_BaseIO_chainTask___redArg(v_task_1780_, v___f_1782_, v___x_1783_, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1786_, lean_object* v_newParserState_1787_, lean_object* v_val_1788_, lean_object* v_sync_1789_, lean_object* v_val_1790_, lean_object* v_a_1791_, lean_object* v_oldResult_1792_, lean_object* v___y_1793_){
_start:
{
uint8_t v_sync_boxed_1794_; lean_object* v_res_1795_; 
v_sync_boxed_1794_ = lean_unbox(v_sync_1789_);
v_res_1795_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1786_, v_newParserState_1787_, v_val_1788_, v_sync_boxed_1794_, v_val_1790_, v_a_1791_, v_oldResult_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1795_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1798_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1800_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1809_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1810_ = l_Lean_Name_append(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1814_, lean_object* v_val_1815_, lean_object* v_fst_1816_, uint8_t v_val_1817_, lean_object* v_a_1818_, lean_object* v_snd_1819_, lean_object* v___x_1820_, uint8_t v___x_1821_, lean_object* v_fst_1822_, lean_object* v_val_1823_, lean_object* v_val_1824_, lean_object* v_val_1825_, lean_object* v_snd_1826_, lean_object* v_prom_1827_, lean_object* v___x_1828_, lean_object* v___f_1829_, lean_object* v___f_1830_, lean_object* v___f_1831_, lean_object* v_pos_1832_, lean_object* v_fst_1833_, lean_object* v_cmdState_1834_, lean_object* v_opts_1835_, lean_object* v___x_1836_, lean_object* v_old_x3f_1837_, lean_object* v_parseCancelTk_1838_, lean_object* v_next_x3f_1839_){
_start:
{
lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v_snapshotTasks_1846_; lean_object* v___y_1847_; lean_object* v_traceTask_1848_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; size_t v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v_env_1884_; lean_object* v_messages_1885_; lean_object* v_scopes_1886_; lean_object* v_infoState_1887_; lean_object* v_traceState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_reportedCmdState_1897_; size_t v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v_reportedCmdState_1954_; size_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; size_t v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_2017_; 
if (lean_obj_tag(v_next_x3f_1839_) == 0)
{
lean_object* v___x_2070_; 
lean_dec(v_parseCancelTk_1838_);
v___x_2070_ = lean_box(0);
v___y_2017_ = v___x_2070_;
goto v___jp_2016_;
}
else
{
lean_object* v_toProcessingContext_2071_; lean_object* v_val_2072_; lean_object* v_pos_2073_; lean_object* v_endPos_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_toProcessingContext_2071_ = lean_ctor_get(v_a_1818_, 0);
v_val_2072_ = lean_ctor_get(v_next_x3f_1839_, 0);
v_pos_2073_ = lean_ctor_get(v_fst_1816_, 0);
v_endPos_2074_ = lean_ctor_get(v_toProcessingContext_2071_, 3);
v___x_2075_ = lean_box(0);
lean_inc(v_endPos_2074_);
lean_inc(v_pos_2073_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_pos_2073_);
lean_ctor_set(v___x_2076_, 1, v_endPos_2074_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_parseCancelTk_1838_);
v___x_2079_ = l_IO_Promise_result_x21___redArg(v_val_2072_);
v___x_2080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2075_);
lean_ctor_set(v___x_2080_, 1, v___x_2077_);
lean_ctor_set(v___x_2080_, 2, v___x_2078_);
lean_ctor_set(v___x_2080_, 3, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
v___y_2017_ = v___x_2081_;
goto v___jp_2016_;
}
v___jp_1841_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1849_, 0, v___y_1843_);
lean_ctor_set(v___x_1849_, 1, v___x_1814_);
lean_ctor_set(v___x_1849_, 2, v___y_1844_);
lean_ctor_set(v___x_1849_, 3, v_traceTask_1848_);
v___x_1850_ = lean_array_push(v_snapshotTasks_1846_, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1847_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_io_promise_resolve(v___x_1851_, v_val_1815_);
if (lean_obj_tag(v_next_x3f_1839_) == 1)
{
lean_object* v_val_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_val_1853_ = lean_ctor_get(v_next_x3f_1839_, 0);
lean_inc(v_val_1853_);
lean_dec_ref(v_next_x3f_1839_);
v___x_1854_ = lean_box(0);
v___x_1855_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1854_, v_fst_1816_, v___y_1845_, v_val_1853_, v_val_1817_, v___y_1842_, v_a_1818_);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1842_);
lean_dec(v_next_x3f_1839_);
lean_dec_ref(v_fst_1816_);
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
}
v___jp_1857_:
{
lean_object* v_snapshotTasks_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_snapshotTasks_1864_ = lean_ctor_get(v___y_1862_, 10);
lean_inc_ref(v_snapshotTasks_1864_);
v___x_1865_ = lean_mk_empty_array_with_capacity(v___y_1859_);
lean_dec(v___y_1859_);
lean_inc_ref(v___y_1863_);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1863_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_task_pure(v___x_1866_);
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___y_1860_;
v___y_1844_ = v___y_1861_;
v___y_1845_ = v___y_1862_;
v_snapshotTasks_1846_ = v_snapshotTasks_1864_;
v___y_1847_ = v___y_1863_;
v_traceTask_1848_ = v___x_1867_;
goto v___jp_1841_;
}
v___jp_1868_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_opts_1907_; uint8_t v_hasTrace_1908_; 
v___x_1898_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1885_);
v___x_1899_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1899_, 0, v___y_1877_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
lean_ctor_set(v___x_1899_, 2, v___y_1878_);
lean_ctor_set(v___x_1899_, 3, v_traceState_1888_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*4, v_val_1817_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v_reportedCmdState_1897_);
v___x_1901_ = lean_io_promise_resolve(v___x_1900_, v_val_1824_);
v___x_1902_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1887_);
lean_inc(v___y_1893_);
v___x_1903_ = l_BaseIO_chainTask___redArg(v___x_1902_, v___y_1879_, v___y_1893_, v___x_1821_);
v___x_1904_ = l_Lean_inheritedTraceOptions;
v___x_1905_ = lean_st_ref_get(v___x_1904_);
v___x_1906_ = l_List_head_x21___redArg(v___x_1828_, v_scopes_1886_);
lean_dec(v_scopes_1886_);
v_opts_1907_ = lean_ctor_get(v___x_1906_, 1);
lean_inc_ref(v_opts_1907_);
lean_dec(v___x_1906_);
v_hasTrace_1908_ = lean_ctor_get_uint8(v_opts_1907_, sizeof(void*)*1);
if (v_hasTrace_1908_ == 0)
{
lean_dec_ref(v_opts_1907_);
lean_dec(v___x_1905_);
lean_dec(v___y_1894_);
lean_dec(v___y_1891_);
lean_dec_ref(v_snapshotTasks_1889_);
lean_dec_ref(v_env_1884_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v_pos_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec_ref(v___f_1829_);
lean_dec(v___x_1820_);
v___y_1858_ = v___y_1892_;
v___y_1859_ = v___y_1893_;
v___y_1860_ = v___y_1895_;
v___y_1861_ = v___y_1896_;
v___y_1862_ = v___y_1883_;
v___y_1863_ = v___y_1890_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1905_, v_opts_1907_, v___x_1909_);
lean_dec(v___x_1905_);
if (v___x_1910_ == 0)
{
lean_dec_ref(v_opts_1907_);
lean_dec(v___y_1894_);
lean_dec(v___y_1891_);
lean_dec_ref(v_snapshotTasks_1889_);
lean_dec_ref(v_env_1884_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v_pos_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec_ref(v___f_1829_);
lean_dec(v___x_1820_);
v___y_1858_ = v___y_1892_;
v___y_1859_ = v___y_1893_;
v___y_1860_ = v___y_1895_;
v___y_1861_ = v___y_1896_;
v___y_1862_ = v___y_1883_;
v___y_1863_ = v___y_1890_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
lean_inc(v___y_1893_);
v___x_1911_ = lean_task_map(v___f_1829_, v___y_1881_, v___y_1893_, v___x_1821_);
lean_inc(v___y_1896_);
lean_inc(v___y_1891_);
lean_inc(v___y_1894_);
v___x_1912_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1912_, 0, v___y_1894_);
lean_ctor_set(v___x_1912_, 1, v___y_1891_);
lean_ctor_set(v___x_1912_, 2, v___y_1896_);
lean_ctor_set(v___x_1912_, 3, v___x_1911_);
lean_inc(v___y_1893_);
v___x_1913_ = lean_task_map(v___f_1830_, v___y_1882_, v___y_1893_, v___x_1821_);
lean_inc(v___y_1896_);
lean_inc(v___y_1891_);
lean_inc(v___y_1894_);
v___x_1914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1894_);
lean_ctor_set(v___x_1914_, 1, v___y_1891_);
lean_ctor_set(v___x_1914_, 2, v___y_1896_);
lean_ctor_set(v___x_1914_, 3, v___x_1913_);
lean_inc(v___y_1893_);
v___x_1915_ = lean_task_map(v___f_1831_, v___y_1880_, v___y_1893_, v___x_1821_);
lean_inc(v___y_1896_);
v___x_1916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1916_, 0, v___y_1894_);
lean_ctor_set(v___x_1916_, 1, v___y_1891_);
lean_ctor_set(v___x_1916_, 2, v___y_1896_);
lean_ctor_set(v___x_1916_, 3, v___x_1915_);
v___x_1917_ = lean_unsigned_to_nat(3u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1912_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1914_);
v___x_1921_ = lean_array_push(v___x_1920_, v___x_1916_);
v___x_1922_ = l_Array_append___redArg(v___x_1921_, v_snapshotTasks_1889_);
lean_inc_ref(v___y_1890_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___y_1890_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_inc_ref(v___x_1923_);
v___x_1924_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1923_);
v___x_1925_ = lean_box_usize(v___y_1869_);
v___x_1926_ = lean_box(v___x_1821_);
v___x_1927_ = lean_box(v_val_1817_);
v___x_1928_ = lean_box(v___x_1910_);
lean_inc_ref(v_a_1818_);
v___f_1929_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_1929_, 0, v___x_1820_);
lean_closure_set(v___f_1929_, 1, v___y_1872_);
lean_closure_set(v___f_1929_, 2, v___y_1871_);
lean_closure_set(v___f_1929_, 3, v___x_1925_);
lean_closure_set(v___f_1929_, 4, v___x_1926_);
lean_closure_set(v___f_1929_, 5, v_env_1884_);
lean_closure_set(v___f_1929_, 6, v___y_1875_);
lean_closure_set(v___f_1929_, 7, v___x_1904_);
lean_closure_set(v___f_1929_, 8, v_a_1818_);
lean_closure_set(v___f_1929_, 9, v_opts_1907_);
lean_closure_set(v___f_1929_, 10, v___x_1923_);
lean_closure_set(v___f_1929_, 11, v_pos_1832_);
lean_closure_set(v___f_1929_, 12, v___x_1927_);
lean_closure_set(v___f_1929_, 13, v___y_1876_);
lean_closure_set(v___f_1929_, 14, v___y_1874_);
lean_closure_set(v___f_1929_, 15, v___y_1873_);
lean_closure_set(v___f_1929_, 16, v___y_1870_);
lean_closure_set(v___f_1929_, 17, v___x_1928_);
v___x_1930_ = lean_io_bind_task(v___x_1924_, v___f_1929_, v___y_1893_, v_val_1817_);
v___y_1842_ = v___y_1892_;
v___y_1843_ = v___y_1895_;
v___y_1844_ = v___y_1896_;
v___y_1845_ = v___y_1883_;
v_snapshotTasks_1846_ = v_snapshotTasks_1889_;
v___y_1847_ = v___y_1890_;
v_traceTask_1848_ = v___x_1930_;
goto v___jp_1841_;
}
}
}
v___jp_1931_:
{
lean_object* v_env_1955_; lean_object* v_messages_1956_; lean_object* v_scopes_1957_; lean_object* v_infoState_1958_; lean_object* v_traceState_1959_; lean_object* v_snapshotTasks_1960_; 
v_env_1955_ = lean_ctor_get(v___y_1946_, 0);
lean_inc_ref(v_env_1955_);
v_messages_1956_ = lean_ctor_get(v___y_1946_, 1);
lean_inc_ref(v_messages_1956_);
v_scopes_1957_ = lean_ctor_get(v___y_1946_, 2);
lean_inc(v_scopes_1957_);
v_infoState_1958_ = lean_ctor_get(v___y_1946_, 8);
lean_inc_ref(v_infoState_1958_);
v_traceState_1959_ = lean_ctor_get(v___y_1946_, 9);
lean_inc_ref(v_traceState_1959_);
v_snapshotTasks_1960_ = lean_ctor_get(v___y_1946_, 10);
lean_inc_ref(v_snapshotTasks_1960_);
v___y_1869_ = v___y_1932_;
v___y_1870_ = v___y_1933_;
v___y_1871_ = v___y_1935_;
v___y_1872_ = v___y_1934_;
v___y_1873_ = v___y_1937_;
v___y_1874_ = v___y_1936_;
v___y_1875_ = v___y_1938_;
v___y_1876_ = v___y_1939_;
v___y_1877_ = v___y_1940_;
v___y_1878_ = v___y_1941_;
v___y_1879_ = v___y_1942_;
v___y_1880_ = v___y_1943_;
v___y_1881_ = v___y_1944_;
v___y_1882_ = v___y_1945_;
v___y_1883_ = v___y_1946_;
v_env_1884_ = v_env_1955_;
v_messages_1885_ = v_messages_1956_;
v_scopes_1886_ = v_scopes_1957_;
v_infoState_1887_ = v_infoState_1958_;
v_traceState_1888_ = v_traceState_1959_;
v_snapshotTasks_1889_ = v_snapshotTasks_1960_;
v___y_1890_ = v___y_1947_;
v___y_1891_ = v___y_1948_;
v___y_1892_ = v___y_1949_;
v___y_1893_ = v___y_1950_;
v___y_1894_ = v___y_1951_;
v___y_1895_ = v___y_1952_;
v___y_1896_ = v___y_1953_;
v_reportedCmdState_1897_ = v_reportedCmdState_1954_;
goto v___jp_1868_;
}
v___jp_1961_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; uint8_t v___x_1991_; 
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1985_);
lean_ctor_set(v___x_1986_, 1, v_val_1823_);
lean_inc_ref(v_a_1818_);
lean_inc(v___y_1979_);
lean_inc(v_pos_1832_);
lean_inc(v_fst_1833_);
v___x_1987_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1833_, v_cmdState_1834_, v_pos_1832_, v___x_1986_, v___y_1979_, v_a_1818_);
v___x_1988_ = lean_box(v_val_1817_);
v___x_1989_ = lean_box(v___x_1821_);
lean_inc(v_pos_1832_);
lean_inc_ref(v_a_1818_);
lean_inc(v___y_1965_);
lean_inc_ref(v___x_1828_);
lean_inc_ref(v___x_1987_);
lean_inc_ref(v___y_1968_);
lean_inc_ref(v___y_1969_);
v___f_1990_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1990_, 0, v___y_1969_);
lean_closure_set(v___f_1990_, 1, v___y_1968_);
lean_closure_set(v___f_1990_, 2, v___x_1988_);
lean_closure_set(v___f_1990_, 3, v_val_1825_);
lean_closure_set(v___f_1990_, 4, v___x_1987_);
lean_closure_set(v___f_1990_, 5, v___x_1828_);
lean_closure_set(v___f_1990_, 6, v___y_1965_);
lean_closure_set(v___f_1990_, 7, v___x_1989_);
lean_closure_set(v___f_1990_, 8, v_a_1818_);
lean_closure_set(v___f_1990_, 9, v_pos_1832_);
v___x_1991_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1835_, v___x_1836_);
if (v___x_1991_ == 0)
{
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_fst_1833_);
lean_inc_ref(v___x_1987_);
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___f_1990_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___y_1976_;
v___y_1946_ = v___x_1987_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1984_;
v_reportedCmdState_1954_ = v___x_1987_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Lean_Parser_isTerminalCommand(v_fst_1833_);
if (v___x_1992_ == 0)
{
if (v___x_1991_ == 0)
{
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_inc_ref(v___x_1987_);
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___f_1990_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___y_1976_;
v___y_1946_ = v___x_1987_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1984_;
v_reportedCmdState_1954_ = v___x_1987_;
goto v___jp_1931_;
}
else
{
lean_object* v_env_1993_; lean_object* v_messages_1994_; lean_object* v_scopes_1995_; lean_object* v_infoState_1996_; lean_object* v_traceState_1997_; lean_object* v_snapshotTasks_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_env_1993_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1993_);
v_messages_1994_ = lean_ctor_get(v___x_1987_, 1);
lean_inc_ref(v_messages_1994_);
v_scopes_1995_ = lean_ctor_get(v___x_1987_, 2);
lean_inc(v_scopes_1995_);
v_infoState_1996_ = lean_ctor_get(v___x_1987_, 8);
lean_inc_ref(v_infoState_1996_);
v_traceState_1997_ = lean_ctor_get(v___x_1987_, 9);
lean_inc_ref(v_traceState_1997_);
v_snapshotTasks_1998_ = lean_ctor_get(v___x_1987_, 10);
lean_inc_ref(v_snapshotTasks_1998_);
v___x_1999_ = lean_mk_empty_array_with_capacity(v___y_1973_);
lean_dec(v___y_1973_);
lean_inc_ref(v___x_1999_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_inc_n(v___y_1980_, 2);
v___x_2001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_1999_);
lean_ctor_set(v___x_2001_, 2, v___y_1980_);
lean_ctor_set(v___x_2001_, 3, v___y_1980_);
lean_ctor_set_usize(v___x_2001_, 4, v___y_1983_);
v___x_2002_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2001_, 2);
v___x_2003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2001_);
lean_ctor_set(v___x_2003_, 2, v___x_2002_);
v___x_2004_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2005_ = l_Lean_Options_empty;
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_mk_empty_array_with_capacity(v___y_1980_);
lean_inc_ref_n(v___x_2007_, 2);
lean_inc(v___x_1820_);
v___x_2008_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2008_, 0, v___x_2004_);
lean_ctor_set(v___x_2008_, 1, v___x_2005_);
lean_ctor_set(v___x_2008_, 2, v___x_1820_);
lean_ctor_set(v___x_2008_, 3, v___x_2006_);
lean_ctor_set(v___x_2008_, 4, v___x_2006_);
lean_ctor_set(v___x_2008_, 5, v___x_2007_);
lean_ctor_set(v___x_2008_, 6, v___x_2007_);
lean_ctor_set(v___x_2008_, 7, v___x_2006_);
lean_ctor_set(v___x_2008_, 8, v___x_2006_);
lean_ctor_set(v___x_2008_, 9, v___x_2006_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*10, v_val_1817_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*10 + 1, v_val_1817_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*10 + 2, v_val_1817_);
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v___x_2006_);
v___x_2010_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2011_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
lean_inc(v___x_1820_);
v___x_2012_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1820_);
v___x_2013_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
lean_ctor_set(v___x_2014_, 2, v___x_2001_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*3, v___x_1821_);
lean_inc(v___y_1980_);
lean_inc_ref(v_env_1993_);
v___x_2015_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2015_, 0, v_env_1993_);
lean_ctor_set(v___x_2015_, 1, v___x_2003_);
lean_ctor_set(v___x_2015_, 2, v___x_2009_);
lean_ctor_set(v___x_2015_, 3, v___x_2002_);
lean_ctor_set(v___x_2015_, 4, v___x_2010_);
lean_ctor_set(v___x_2015_, 5, v___y_1980_);
lean_ctor_set(v___x_2015_, 6, v___x_2011_);
lean_ctor_set(v___x_2015_, 7, v___x_2012_);
lean_ctor_set(v___x_2015_, 8, v___x_2014_);
lean_ctor_set(v___x_2015_, 9, v___y_1972_);
lean_ctor_set(v___x_2015_, 10, v___x_2007_);
v___y_1869_ = v___y_1962_;
v___y_1870_ = v___y_1963_;
v___y_1871_ = v___y_1965_;
v___y_1872_ = v___y_1964_;
v___y_1873_ = v___y_1966_;
v___y_1874_ = v___y_1967_;
v___y_1875_ = v___y_1968_;
v___y_1876_ = v___y_1969_;
v___y_1877_ = v___y_1970_;
v___y_1878_ = v___y_1971_;
v___y_1879_ = v___f_1990_;
v___y_1880_ = v___y_1974_;
v___y_1881_ = v___y_1975_;
v___y_1882_ = v___y_1976_;
v___y_1883_ = v___x_1987_;
v_env_1884_ = v_env_1993_;
v_messages_1885_ = v_messages_1994_;
v_scopes_1886_ = v_scopes_1995_;
v_infoState_1887_ = v_infoState_1996_;
v_traceState_1888_ = v_traceState_1997_;
v_snapshotTasks_1889_ = v_snapshotTasks_1998_;
v___y_1890_ = v___y_1977_;
v___y_1891_ = v___y_1978_;
v___y_1892_ = v___y_1979_;
v___y_1893_ = v___y_1980_;
v___y_1894_ = v___y_1981_;
v___y_1895_ = v___y_1982_;
v___y_1896_ = v___y_1984_;
v_reportedCmdState_1897_ = v___x_2015_;
goto v___jp_1868_;
}
}
else
{
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_inc_ref(v___x_1987_);
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___f_1990_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___y_1976_;
v___y_1946_ = v___x_1987_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1984_;
v_reportedCmdState_1954_ = v___x_1987_;
goto v___jp_1931_;
}
}
}
v___jp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2018_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1819_);
v___x_2019_ = l_IO_CancelToken_new();
v___x_2020_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1820_);
v___x_2021_ = l_Lean_Name_str___override(v___x_1820_, v___x_2020_);
v___x_2022_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2023_ = l_Lean_Name_str___override(v___x_2021_, v___x_2022_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2025_ = l_Lean_Name_str___override(v___x_2023_, v___x_2024_);
v___x_2026_ = l_Lean_Name_str___override(v___x_2025_, v___x_2022_);
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = l_Lean_Name_num___override(v___x_2026_, v___x_2027_);
v___x_2029_ = l_Lean_Name_str___override(v___x_2028_, v___x_2022_);
v___x_2030_ = l_Lean_Name_str___override(v___x_2029_, v___x_2024_);
v___x_2031_ = l_Lean_Name_str___override(v___x_2030_, v___x_2022_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2033_ = l_Lean_Name_str___override(v___x_2031_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2035_ = l_Lean_Name_str___override(v___x_2033_, v___x_2034_);
v___x_2036_ = l_Lean_Name_toString(v___x_2035_, v___x_1821_);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_unsigned_to_nat(32u);
v___x_2039_ = ((size_t)5ULL);
v___x_2040_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref(v___x_2036_);
v___x_2041_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2041_, 0, v___x_2036_);
lean_ctor_set(v___x_2041_, 1, v___x_2018_);
lean_ctor_set(v___x_2041_, 2, v___x_2037_);
lean_ctor_set(v___x_2041_, 3, v___x_2040_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*4, v_val_1817_);
v___x_2042_ = l_Lean_Language_Snapshot_Diagnostics_empty;
lean_inc_ref(v___x_2036_);
v___x_2043_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2043_, 0, v___x_2036_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
lean_ctor_set(v___x_2043_, 2, v___x_2037_);
lean_ctor_set(v___x_2043_, 3, v___x_2040_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*4, v_val_1817_);
lean_inc(v_fst_1822_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_fst_1822_);
v___x_2045_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2044_);
lean_inc(v___x_2019_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2019_);
v___x_2047_ = l_IO_Promise_result_x21___redArg(v_val_1823_);
lean_inc_ref(v___x_2047_);
lean_inc(v___x_2045_);
lean_inc_ref(v___x_2044_);
v___x_2048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2044_);
lean_ctor_set(v___x_2048_, 1, v___x_2045_);
lean_ctor_set(v___x_2048_, 2, v___x_2046_);
lean_ctor_set(v___x_2048_, 3, v___x_2047_);
v___x_2049_ = l_IO_Promise_result_x21___redArg(v_val_1824_);
lean_inc_ref(v___x_2049_);
lean_inc(v___x_1814_);
lean_inc_ref(v___x_2044_);
v___x_2050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2044_);
lean_ctor_set(v___x_2050_, 1, v___x_1814_);
lean_ctor_set(v___x_2050_, 2, v___x_2037_);
lean_ctor_set(v___x_2050_, 3, v___x_2049_);
v___x_2051_ = l_IO_Promise_result_x21___redArg(v_val_1825_);
lean_inc_ref(v___x_2051_);
lean_inc(v___x_1814_);
lean_inc_ref(v___x_2044_);
v___x_2052_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2044_);
lean_ctor_set(v___x_2052_, 1, v___x_1814_);
lean_ctor_set(v___x_2052_, 2, v___x_2037_);
lean_ctor_set(v___x_2052_, 3, v___x_2051_);
v___x_2053_ = l_IO_Promise_result_x21___redArg(v_val_1815_);
lean_inc(v___x_1814_);
v___x_2054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2037_);
lean_ctor_set(v___x_2054_, 1, v___x_1814_);
lean_ctor_set(v___x_2054_, 2, v___x_2037_);
lean_ctor_set(v___x_2054_, 3, v___x_2053_);
lean_inc_ref(v___x_2043_);
v___x_2055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2043_);
lean_ctor_set(v___x_2055_, 1, v___x_2048_);
lean_ctor_set(v___x_2055_, 2, v___x_2050_);
lean_ctor_set(v___x_2055_, 3, v___x_2052_);
lean_ctor_set(v___x_2055_, 4, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2041_);
lean_ctor_set(v___x_2056_, 1, v_fst_1822_);
lean_ctor_set(v___x_2056_, 2, v_snd_1826_);
lean_ctor_set(v___x_2056_, 3, v___x_2055_);
lean_ctor_set(v___x_2056_, 4, v___y_2017_);
v___x_2057_ = lean_io_promise_resolve(v___x_2056_, v_prom_1827_);
if (lean_obj_tag(v_old_x3f_1837_) == 0)
{
lean_inc_ref(v___x_2036_);
lean_inc_ref(v___x_2043_);
v___y_1962_ = v___x_2039_;
v___y_1963_ = v___x_2037_;
v___y_1964_ = v___x_2038_;
v___y_1965_ = v___x_2027_;
v___y_1966_ = v___x_2043_;
v___y_1967_ = v___x_2037_;
v___y_1968_ = v___x_2040_;
v___y_1969_ = v___x_2036_;
v___y_1970_ = v___x_2036_;
v___y_1971_ = v___x_2037_;
v___y_1972_ = v___x_2040_;
v___y_1973_ = v___x_2038_;
v___y_1974_ = v___x_2051_;
v___y_1975_ = v___x_2047_;
v___y_1976_ = v___x_2049_;
v___y_1977_ = v___x_2043_;
v___y_1978_ = v___x_2045_;
v___y_1979_ = v___x_2019_;
v___y_1980_ = v___x_2027_;
v___y_1981_ = v___x_2044_;
v___y_1982_ = v___x_2037_;
v___y_1983_ = v___x_2039_;
v___y_1984_ = v___x_2037_;
v___y_1985_ = v___x_2037_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2069_; 
v_val_2058_ = lean_ctor_get(v_old_x3f_1837_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_old_x3f_1837_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2060_ = v_old_x3f_1837_;
v_isShared_2061_ = v_isSharedCheck_2069_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_val_2058_);
lean_dec(v_old_x3f_1837_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2069_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_elabSnap_2062_; lean_object* v_stx_2063_; lean_object* v_elabSnap_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_elabSnap_2062_ = lean_ctor_get(v_val_2058_, 3);
lean_inc_ref(v_elabSnap_2062_);
v_stx_2063_ = lean_ctor_get(v_val_2058_, 1);
lean_inc(v_stx_2063_);
lean_dec(v_val_2058_);
v_elabSnap_2064_ = lean_ctor_get(v_elabSnap_2062_, 1);
lean_inc_ref(v_elabSnap_2064_);
lean_dec_ref(v_elabSnap_2062_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_stx_2063_);
lean_ctor_set(v___x_2065_, 1, v_elabSnap_2064_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2065_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_inc_ref(v___x_2036_);
lean_inc_ref(v___x_2043_);
v___y_1962_ = v___x_2039_;
v___y_1963_ = v___x_2037_;
v___y_1964_ = v___x_2038_;
v___y_1965_ = v___x_2027_;
v___y_1966_ = v___x_2043_;
v___y_1967_ = v___x_2037_;
v___y_1968_ = v___x_2040_;
v___y_1969_ = v___x_2036_;
v___y_1970_ = v___x_2036_;
v___y_1971_ = v___x_2037_;
v___y_1972_ = v___x_2040_;
v___y_1973_ = v___x_2038_;
v___y_1974_ = v___x_2051_;
v___y_1975_ = v___x_2047_;
v___y_1976_ = v___x_2049_;
v___y_1977_ = v___x_2043_;
v___y_1978_ = v___x_2045_;
v___y_1979_ = v___x_2019_;
v___y_1980_ = v___x_2027_;
v___y_1981_ = v___x_2044_;
v___y_1982_ = v___x_2037_;
v___y_1983_ = v___x_2039_;
v___y_1984_ = v___x_2037_;
v___y_1985_ = v___x_2067_;
goto v___jp_1961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2082_, uint8_t v_val_2083_, lean_object* v_a_2084_, lean_object* v_snd_2085_, lean_object* v___x_2086_, uint8_t v___x_2087_, lean_object* v_prom_2088_, lean_object* v___x_2089_, lean_object* v___f_2090_, lean_object* v___f_2091_, lean_object* v___f_2092_, lean_object* v_pos_2093_, lean_object* v_fst_2094_, lean_object* v_cmdState_2095_, lean_object* v_opts_2096_, lean_object* v_old_x3f_2097_, lean_object* v_parseCancelTk_2098_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v_snapshotTasks_2111_; lean_object* v___y_2112_; lean_object* v_traceTask_2113_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; size_t v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v_env_2149_; lean_object* v_messages_2150_; lean_object* v_scopes_2151_; lean_object* v_infoState_2152_; lean_object* v_traceState_2153_; lean_object* v_snapshotTasks_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v_reportedCmdState_2166_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; size_t v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v_reportedCmdState_2225_; lean_object* v___x_2232_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; size_t v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; size_t v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v_fst_2369_; lean_object* v_snd_2370_; uint8_t v___y_2383_; uint8_t v___x_2386_; 
v___x_2100_ = lean_io_promise_new();
v___x_2101_ = lean_io_promise_new();
v___x_2102_ = lean_io_promise_new();
v___x_2103_ = lean_io_promise_new();
v___x_2232_ = l_Lean_internal_cmdlineSnapshots;
v___x_2386_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2096_, v___x_2232_);
if (v___x_2386_ == 0)
{
v___y_2383_ = v___x_2386_;
goto v___jp_2382_;
}
else
{
uint8_t v___x_2387_; 
lean_inc(v_fst_2094_);
v___x_2387_ = l_Lean_Parser_isTerminalCommand(v_fst_2094_);
if (v___x_2387_ == 0)
{
v___y_2383_ = v___x_2386_;
goto v___jp_2382_;
}
else
{
lean_inc_ref(v_fst_2082_);
lean_inc(v_fst_2094_);
v_fst_2369_ = v_fst_2094_;
v_snd_2370_ = v_fst_2082_;
goto v___jp_2368_;
}
}
v___jp_2104_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2114_, 0, v___y_2107_);
lean_ctor_set(v___x_2114_, 1, v___y_2109_);
lean_ctor_set(v___x_2114_, 2, v___y_2112_);
lean_ctor_set(v___x_2114_, 3, v_traceTask_2113_);
v___x_2115_ = lean_array_push(v_snapshotTasks_2111_, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___y_2105_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_io_promise_resolve(v___x_2116_, v___x_2103_);
lean_dec(v___x_2103_);
if (lean_obj_tag(v___y_2106_) == 1)
{
lean_object* v_val_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_val_2118_ = lean_ctor_get(v___y_2106_, 0);
lean_inc(v_val_2118_);
lean_dec_ref(v___y_2106_);
v___x_2119_ = lean_box(0);
v___x_2120_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2119_, v_fst_2082_, v___y_2110_, v_val_2118_, v_val_2083_, v___y_2108_, v_a_2084_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; 
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2108_);
lean_dec(v___y_2106_);
lean_dec_ref(v_fst_2082_);
v___x_2121_ = lean_box(0);
return v___x_2121_;
}
}
v___jp_2122_:
{
lean_object* v_snapshotTasks_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_snapshotTasks_2131_ = lean_ctor_get(v___y_2128_, 10);
lean_inc_ref(v_snapshotTasks_2131_);
v___x_2132_ = lean_mk_empty_array_with_capacity(v___y_2130_);
lean_dec(v___y_2130_);
lean_inc_ref(v___y_2123_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___y_2123_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_task_pure(v___x_2133_);
v___y_2105_ = v___y_2123_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v___y_2124_;
v___y_2108_ = v___y_2127_;
v___y_2109_ = v___y_2126_;
v___y_2110_ = v___y_2128_;
v_snapshotTasks_2111_ = v_snapshotTasks_2131_;
v___y_2112_ = v___y_2129_;
v_traceTask_2113_ = v___x_2134_;
goto v___jp_2104_;
}
v___jp_2135_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_opts_2176_; uint8_t v_hasTrace_2177_; 
v___x_2167_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2150_);
v___x_2168_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2168_, 0, v___y_2159_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
lean_ctor_set(v___x_2168_, 2, v___y_2146_);
lean_ctor_set(v___x_2168_, 3, v_traceState_2153_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*4, v_val_2083_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v_reportedCmdState_2166_);
v___x_2170_ = lean_io_promise_resolve(v___x_2169_, v___x_2101_);
lean_dec(v___x_2101_);
v___x_2171_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2152_);
lean_inc(v___y_2155_);
v___x_2172_ = l_BaseIO_chainTask___redArg(v___x_2171_, v___y_2158_, v___y_2155_, v___x_2087_);
v___x_2173_ = l_Lean_inheritedTraceOptions;
v___x_2174_ = lean_st_ref_get(v___x_2173_);
v___x_2175_ = l_List_head_x21___redArg(v___x_2089_, v_scopes_2151_);
lean_dec(v_scopes_2151_);
v_opts_2176_ = lean_ctor_get(v___x_2175_, 1);
lean_inc_ref(v_opts_2176_);
lean_dec(v___x_2175_);
v_hasTrace_2177_ = lean_ctor_get_uint8(v_opts_2176_, sizeof(void*)*1);
if (v_hasTrace_2177_ == 0)
{
lean_dec_ref(v_opts_2176_);
lean_dec(v___x_2174_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_snapshotTasks_2154_);
lean_dec_ref(v_env_2149_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v_pos_2093_);
lean_dec_ref(v___f_2092_);
lean_dec_ref(v___f_2091_);
lean_dec_ref(v___f_2090_);
lean_dec(v___x_2086_);
v___y_2123_ = v___y_2145_;
v___y_2124_ = v___y_2160_;
v___y_2125_ = v___y_2161_;
v___y_2126_ = v___y_2162_;
v___y_2127_ = v___y_2163_;
v___y_2128_ = v___y_2148_;
v___y_2129_ = v___y_2165_;
v___y_2130_ = v___y_2155_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2174_, v_opts_2176_, v___x_2178_);
lean_dec(v___x_2174_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v_opts_2176_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_snapshotTasks_2154_);
lean_dec_ref(v_env_2149_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v_pos_2093_);
lean_dec_ref(v___f_2092_);
lean_dec_ref(v___f_2091_);
lean_dec_ref(v___f_2090_);
lean_dec(v___x_2086_);
v___y_2123_ = v___y_2145_;
v___y_2124_ = v___y_2160_;
v___y_2125_ = v___y_2161_;
v___y_2126_ = v___y_2162_;
v___y_2127_ = v___y_2163_;
v___y_2128_ = v___y_2148_;
v___y_2129_ = v___y_2165_;
v___y_2130_ = v___y_2155_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
lean_inc(v___y_2155_);
v___x_2180_ = lean_task_map(v___f_2090_, v___y_2156_, v___y_2155_, v___x_2087_);
lean_inc(v___y_2165_);
lean_inc(v___y_2164_);
lean_inc(v___y_2147_);
v___x_2181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2147_);
lean_ctor_set(v___x_2181_, 1, v___y_2164_);
lean_ctor_set(v___x_2181_, 2, v___y_2165_);
lean_ctor_set(v___x_2181_, 3, v___x_2180_);
lean_inc(v___y_2155_);
v___x_2182_ = lean_task_map(v___f_2091_, v___y_2144_, v___y_2155_, v___x_2087_);
lean_inc(v___y_2165_);
lean_inc(v___y_2164_);
lean_inc(v___y_2147_);
v___x_2183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2183_, 0, v___y_2147_);
lean_ctor_set(v___x_2183_, 1, v___y_2164_);
lean_ctor_set(v___x_2183_, 2, v___y_2165_);
lean_ctor_set(v___x_2183_, 3, v___x_2182_);
lean_inc(v___y_2155_);
v___x_2184_ = lean_task_map(v___f_2092_, v___y_2157_, v___y_2155_, v___x_2087_);
lean_inc(v___y_2165_);
v___x_2185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2185_, 0, v___y_2147_);
lean_ctor_set(v___x_2185_, 1, v___y_2164_);
lean_ctor_set(v___x_2185_, 2, v___y_2165_);
lean_ctor_set(v___x_2185_, 3, v___x_2184_);
v___x_2186_ = lean_unsigned_to_nat(3u);
v___x_2187_ = lean_mk_empty_array_with_capacity(v___x_2186_);
v___x_2188_ = lean_array_push(v___x_2187_, v___x_2181_);
v___x_2189_ = lean_array_push(v___x_2188_, v___x_2183_);
v___x_2190_ = lean_array_push(v___x_2189_, v___x_2185_);
v___x_2191_ = l_Array_append___redArg(v___x_2190_, v_snapshotTasks_2154_);
lean_inc_ref(v___y_2145_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___y_2145_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_inc_ref(v___x_2192_);
v___x_2193_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2192_);
v___x_2194_ = lean_box_usize(v___y_2142_);
v___x_2195_ = lean_box(v___x_2087_);
v___x_2196_ = lean_box(v_val_2083_);
v___x_2197_ = lean_box(v___x_2179_);
lean_inc_ref(v_a_2084_);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2198_, 0, v___x_2086_);
lean_closure_set(v___f_2198_, 1, v___y_2143_);
lean_closure_set(v___f_2198_, 2, v___y_2136_);
lean_closure_set(v___f_2198_, 3, v___x_2194_);
lean_closure_set(v___f_2198_, 4, v___x_2195_);
lean_closure_set(v___f_2198_, 5, v_env_2149_);
lean_closure_set(v___f_2198_, 6, v___y_2137_);
lean_closure_set(v___f_2198_, 7, v___x_2173_);
lean_closure_set(v___f_2198_, 8, v_a_2084_);
lean_closure_set(v___f_2198_, 9, v_opts_2176_);
lean_closure_set(v___f_2198_, 10, v___x_2192_);
lean_closure_set(v___f_2198_, 11, v_pos_2093_);
lean_closure_set(v___f_2198_, 12, v___x_2196_);
lean_closure_set(v___f_2198_, 13, v___y_2141_);
lean_closure_set(v___f_2198_, 14, v___y_2138_);
lean_closure_set(v___f_2198_, 15, v___y_2139_);
lean_closure_set(v___f_2198_, 16, v___y_2140_);
lean_closure_set(v___f_2198_, 17, v___x_2197_);
v___x_2199_ = lean_io_bind_task(v___x_2193_, v___f_2198_, v___y_2155_, v_val_2083_);
v___y_2105_ = v___y_2145_;
v___y_2106_ = v___y_2161_;
v___y_2107_ = v___y_2160_;
v___y_2108_ = v___y_2163_;
v___y_2109_ = v___y_2162_;
v___y_2110_ = v___y_2148_;
v_snapshotTasks_2111_ = v_snapshotTasks_2154_;
v___y_2112_ = v___y_2165_;
v_traceTask_2113_ = v___x_2199_;
goto v___jp_2104_;
}
}
}
v___jp_2200_:
{
lean_object* v_env_2226_; lean_object* v_messages_2227_; lean_object* v_scopes_2228_; lean_object* v_infoState_2229_; lean_object* v_traceState_2230_; lean_object* v_snapshotTasks_2231_; 
v_env_2226_ = lean_ctor_get(v___y_2213_, 0);
lean_inc_ref(v_env_2226_);
v_messages_2227_ = lean_ctor_get(v___y_2213_, 1);
lean_inc_ref(v_messages_2227_);
v_scopes_2228_ = lean_ctor_get(v___y_2213_, 2);
lean_inc(v_scopes_2228_);
v_infoState_2229_ = lean_ctor_get(v___y_2213_, 8);
lean_inc_ref(v_infoState_2229_);
v_traceState_2230_ = lean_ctor_get(v___y_2213_, 9);
lean_inc_ref(v_traceState_2230_);
v_snapshotTasks_2231_ = lean_ctor_get(v___y_2213_, 10);
lean_inc_ref(v_snapshotTasks_2231_);
v___y_2136_ = v___y_2201_;
v___y_2137_ = v___y_2202_;
v___y_2138_ = v___y_2203_;
v___y_2139_ = v___y_2204_;
v___y_2140_ = v___y_2206_;
v___y_2141_ = v___y_2205_;
v___y_2142_ = v___y_2207_;
v___y_2143_ = v___y_2208_;
v___y_2144_ = v___y_2209_;
v___y_2145_ = v___y_2210_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___y_2212_;
v___y_2148_ = v___y_2213_;
v_env_2149_ = v_env_2226_;
v_messages_2150_ = v_messages_2227_;
v_scopes_2151_ = v_scopes_2228_;
v_infoState_2152_ = v_infoState_2229_;
v_traceState_2153_ = v_traceState_2230_;
v_snapshotTasks_2154_ = v_snapshotTasks_2231_;
v___y_2155_ = v___y_2214_;
v___y_2156_ = v___y_2215_;
v___y_2157_ = v___y_2216_;
v___y_2158_ = v___y_2217_;
v___y_2159_ = v___y_2218_;
v___y_2160_ = v___y_2219_;
v___y_2161_ = v___y_2220_;
v___y_2162_ = v___y_2221_;
v___y_2163_ = v___y_2222_;
v___y_2164_ = v___y_2223_;
v___y_2165_ = v___y_2224_;
v_reportedCmdState_2166_ = v_reportedCmdState_2225_;
goto v___jp_2135_;
}
v___jp_2233_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; uint8_t v___x_2265_; 
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2100_);
lean_inc_ref(v_a_2084_);
lean_inc(v___y_2253_);
lean_inc(v_pos_2093_);
lean_inc(v_fst_2094_);
v___x_2261_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2094_, v_cmdState_2095_, v_pos_2093_, v___x_2260_, v___y_2253_, v_a_2084_);
v___x_2262_ = lean_box(v_val_2083_);
v___x_2263_ = lean_box(v___x_2087_);
lean_inc(v_pos_2093_);
lean_inc_ref(v_a_2084_);
lean_inc(v___y_2234_);
lean_inc_ref(v___x_2089_);
lean_inc_ref(v___x_2261_);
lean_inc_ref(v___y_2235_);
lean_inc_ref(v___y_2239_);
v___f_2264_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2264_, 0, v___y_2239_);
lean_closure_set(v___f_2264_, 1, v___y_2235_);
lean_closure_set(v___f_2264_, 2, v___x_2262_);
lean_closure_set(v___f_2264_, 3, v___x_2102_);
lean_closure_set(v___f_2264_, 4, v___x_2261_);
lean_closure_set(v___f_2264_, 5, v___x_2089_);
lean_closure_set(v___f_2264_, 6, v___y_2234_);
lean_closure_set(v___f_2264_, 7, v___x_2263_);
lean_closure_set(v___f_2264_, 8, v_a_2084_);
lean_closure_set(v___f_2264_, 9, v_pos_2093_);
v___x_2265_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2096_, v___x_2232_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2255_);
lean_dec(v_fst_2094_);
lean_inc_ref(v___x_2261_);
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2239_;
v___y_2206_ = v___y_2238_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2241_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2244_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2246_;
v___y_2213_ = v___x_2261_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2264_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2251_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2253_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v_reportedCmdState_2225_ = v___x_2261_;
goto v___jp_2200_;
}
else
{
uint8_t v___x_2266_; 
v___x_2266_ = l_Lean_Parser_isTerminalCommand(v_fst_2094_);
if (v___x_2266_ == 0)
{
if (v___x_2265_ == 0)
{
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2255_);
lean_inc_ref(v___x_2261_);
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2239_;
v___y_2206_ = v___y_2238_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2241_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2244_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2246_;
v___y_2213_ = v___x_2261_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2264_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2251_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2253_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v_reportedCmdState_2225_ = v___x_2261_;
goto v___jp_2200_;
}
else
{
lean_object* v_env_2267_; lean_object* v_messages_2268_; lean_object* v_scopes_2269_; lean_object* v_infoState_2270_; lean_object* v_traceState_2271_; lean_object* v_snapshotTasks_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_env_2267_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_env_2267_);
v_messages_2268_ = lean_ctor_get(v___x_2261_, 1);
lean_inc_ref(v_messages_2268_);
v_scopes_2269_ = lean_ctor_get(v___x_2261_, 2);
lean_inc(v_scopes_2269_);
v_infoState_2270_ = lean_ctor_get(v___x_2261_, 8);
lean_inc_ref(v_infoState_2270_);
v_traceState_2271_ = lean_ctor_get(v___x_2261_, 9);
lean_inc_ref(v_traceState_2271_);
v_snapshotTasks_2272_ = lean_ctor_get(v___x_2261_, 10);
lean_inc_ref(v_snapshotTasks_2272_);
v___x_2273_ = lean_mk_empty_array_with_capacity(v___y_2255_);
lean_dec(v___y_2255_);
lean_inc_ref(v___x_2273_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_inc_n(v___y_2247_, 2);
v___x_2275_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2273_);
lean_ctor_set(v___x_2275_, 2, v___y_2247_);
lean_ctor_set(v___x_2275_, 3, v___y_2247_);
lean_ctor_set_usize(v___x_2275_, 4, v___y_2243_);
v___x_2276_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2275_, 2);
v___x_2277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2275_);
lean_ctor_set(v___x_2277_, 2, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2279_ = l_Lean_Options_empty;
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_mk_empty_array_with_capacity(v___y_2247_);
lean_inc_ref_n(v___x_2281_, 2);
lean_inc(v___x_2086_);
v___x_2282_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2282_, 0, v___x_2278_);
lean_ctor_set(v___x_2282_, 1, v___x_2279_);
lean_ctor_set(v___x_2282_, 2, v___x_2086_);
lean_ctor_set(v___x_2282_, 3, v___x_2280_);
lean_ctor_set(v___x_2282_, 4, v___x_2280_);
lean_ctor_set(v___x_2282_, 5, v___x_2281_);
lean_ctor_set(v___x_2282_, 6, v___x_2281_);
lean_ctor_set(v___x_2282_, 7, v___x_2280_);
lean_ctor_set(v___x_2282_, 8, v___x_2280_);
lean_ctor_set(v___x_2282_, 9, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*10, v_val_2083_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*10 + 1, v_val_2083_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*10 + 2, v_val_2083_);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2280_);
v___x_2284_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2285_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
lean_inc(v___x_2086_);
v___x_2286_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2086_);
v___x_2287_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
lean_ctor_set(v___x_2288_, 2, v___x_2275_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*3, v___x_2087_);
lean_inc(v___y_2247_);
lean_inc_ref(v_env_2267_);
v___x_2289_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2289_, 0, v_env_2267_);
lean_ctor_set(v___x_2289_, 1, v___x_2277_);
lean_ctor_set(v___x_2289_, 2, v___x_2283_);
lean_ctor_set(v___x_2289_, 3, v___x_2276_);
lean_ctor_set(v___x_2289_, 4, v___x_2284_);
lean_ctor_set(v___x_2289_, 5, v___y_2247_);
lean_ctor_set(v___x_2289_, 6, v___x_2285_);
lean_ctor_set(v___x_2289_, 7, v___x_2286_);
lean_ctor_set(v___x_2289_, 8, v___x_2288_);
lean_ctor_set(v___x_2289_, 9, v___y_2258_);
lean_ctor_set(v___x_2289_, 10, v___x_2281_);
v___y_2136_ = v___y_2234_;
v___y_2137_ = v___y_2235_;
v___y_2138_ = v___y_2236_;
v___y_2139_ = v___y_2237_;
v___y_2140_ = v___y_2238_;
v___y_2141_ = v___y_2239_;
v___y_2142_ = v___y_2240_;
v___y_2143_ = v___y_2241_;
v___y_2144_ = v___y_2242_;
v___y_2145_ = v___y_2244_;
v___y_2146_ = v___y_2245_;
v___y_2147_ = v___y_2246_;
v___y_2148_ = v___x_2261_;
v_env_2149_ = v_env_2267_;
v_messages_2150_ = v_messages_2268_;
v_scopes_2151_ = v_scopes_2269_;
v_infoState_2152_ = v_infoState_2270_;
v_traceState_2153_ = v_traceState_2271_;
v_snapshotTasks_2154_ = v_snapshotTasks_2272_;
v___y_2155_ = v___y_2247_;
v___y_2156_ = v___y_2248_;
v___y_2157_ = v___y_2249_;
v___y_2158_ = v___f_2264_;
v___y_2159_ = v___y_2250_;
v___y_2160_ = v___y_2252_;
v___y_2161_ = v___y_2251_;
v___y_2162_ = v___y_2254_;
v___y_2163_ = v___y_2253_;
v___y_2164_ = v___y_2256_;
v___y_2165_ = v___y_2257_;
v_reportedCmdState_2166_ = v___x_2289_;
goto v___jp_2135_;
}
}
else
{
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2255_);
lean_inc_ref(v___x_2261_);
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2239_;
v___y_2206_ = v___y_2238_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2241_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2244_;
v___y_2211_ = v___y_2245_;
v___y_2212_ = v___y_2246_;
v___y_2213_ = v___x_2261_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___f_2264_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2251_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2253_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v_reportedCmdState_2225_ = v___x_2261_;
goto v___jp_2200_;
}
}
}
v___jp_2290_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2296_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2085_);
v___x_2297_ = l_IO_CancelToken_new();
v___x_2298_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2086_);
v___x_2299_ = l_Lean_Name_str___override(v___x_2086_, v___x_2298_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2301_ = l_Lean_Name_str___override(v___x_2299_, v___x_2300_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2303_ = l_Lean_Name_str___override(v___x_2301_, v___x_2302_);
v___x_2304_ = l_Lean_Name_str___override(v___x_2303_, v___x_2300_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = l_Lean_Name_num___override(v___x_2304_, v___x_2305_);
v___x_2307_ = l_Lean_Name_str___override(v___x_2306_, v___x_2300_);
v___x_2308_ = l_Lean_Name_str___override(v___x_2307_, v___x_2302_);
v___x_2309_ = l_Lean_Name_str___override(v___x_2308_, v___x_2300_);
v___x_2310_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2311_ = l_Lean_Name_str___override(v___x_2309_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2313_ = l_Lean_Name_str___override(v___x_2311_, v___x_2312_);
v___x_2314_ = l_Lean_Name_toString(v___x_2313_, v___x_2087_);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_unsigned_to_nat(32u);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
lean_dec_ref(v___x_2317_);
v___x_2318_ = ((size_t)5ULL);
v___x_2319_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref(v___x_2314_);
v___x_2320_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2320_, 0, v___x_2314_);
lean_ctor_set(v___x_2320_, 1, v___x_2296_);
lean_ctor_set(v___x_2320_, 2, v___x_2315_);
lean_ctor_set(v___x_2320_, 3, v___x_2319_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*4, v_val_2083_);
v___x_2321_ = l_Lean_Language_Snapshot_Diagnostics_empty;
lean_inc_ref(v___x_2314_);
v___x_2322_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2322_, 0, v___x_2314_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
lean_ctor_set(v___x_2322_, 2, v___x_2315_);
lean_ctor_set(v___x_2322_, 3, v___x_2319_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*4, v_val_2083_);
lean_inc(v___y_2291_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___y_2291_);
v___x_2324_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2323_);
lean_inc(v___x_2297_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2297_);
v___x_2326_ = l_IO_Promise_result_x21___redArg(v___x_2100_);
lean_inc_ref(v___x_2326_);
lean_inc(v___x_2324_);
lean_inc_ref(v___x_2323_);
v___x_2327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2323_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
lean_ctor_set(v___x_2327_, 2, v___x_2325_);
lean_ctor_set(v___x_2327_, 3, v___x_2326_);
v___x_2328_ = l_IO_Promise_result_x21___redArg(v___x_2101_);
lean_inc_ref(v___x_2328_);
lean_inc(v___y_2293_);
lean_inc_ref(v___x_2323_);
v___x_2329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2323_);
lean_ctor_set(v___x_2329_, 1, v___y_2293_);
lean_ctor_set(v___x_2329_, 2, v___x_2315_);
lean_ctor_set(v___x_2329_, 3, v___x_2328_);
v___x_2330_ = l_IO_Promise_result_x21___redArg(v___x_2102_);
lean_inc_ref(v___x_2330_);
lean_inc(v___y_2293_);
lean_inc_ref(v___x_2323_);
v___x_2331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2323_);
lean_ctor_set(v___x_2331_, 1, v___y_2293_);
lean_ctor_set(v___x_2331_, 2, v___x_2315_);
lean_ctor_set(v___x_2331_, 3, v___x_2330_);
v___x_2332_ = l_IO_Promise_result_x21___redArg(v___x_2103_);
lean_inc(v___y_2293_);
v___x_2333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2315_);
lean_ctor_set(v___x_2333_, 1, v___y_2293_);
lean_ctor_set(v___x_2333_, 2, v___x_2315_);
lean_ctor_set(v___x_2333_, 3, v___x_2332_);
lean_inc_ref(v___x_2322_);
v___x_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2322_);
lean_ctor_set(v___x_2334_, 1, v___x_2327_);
lean_ctor_set(v___x_2334_, 2, v___x_2329_);
lean_ctor_set(v___x_2334_, 3, v___x_2331_);
lean_ctor_set(v___x_2334_, 4, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2320_);
lean_ctor_set(v___x_2335_, 1, v___y_2291_);
lean_ctor_set(v___x_2335_, 2, v___y_2294_);
lean_ctor_set(v___x_2335_, 3, v___x_2334_);
lean_ctor_set(v___x_2335_, 4, v___y_2295_);
v___x_2336_ = lean_io_promise_resolve(v___x_2335_, v_prom_2088_);
if (lean_obj_tag(v_old_x3f_2097_) == 0)
{
lean_inc_ref(v___x_2314_);
lean_inc_ref(v___x_2322_);
v___y_2234_ = v___x_2305_;
v___y_2235_ = v___x_2319_;
v___y_2236_ = v___x_2315_;
v___y_2237_ = v___x_2322_;
v___y_2238_ = v___x_2315_;
v___y_2239_ = v___x_2314_;
v___y_2240_ = v___x_2318_;
v___y_2241_ = v___x_2316_;
v___y_2242_ = v___x_2328_;
v___y_2243_ = v___x_2318_;
v___y_2244_ = v___x_2322_;
v___y_2245_ = v___x_2315_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2305_;
v___y_2248_ = v___x_2326_;
v___y_2249_ = v___x_2330_;
v___y_2250_ = v___x_2314_;
v___y_2251_ = v___y_2292_;
v___y_2252_ = v___x_2315_;
v___y_2253_ = v___x_2297_;
v___y_2254_ = v___y_2293_;
v___y_2255_ = v___x_2316_;
v___y_2256_ = v___x_2324_;
v___y_2257_ = v___x_2315_;
v___y_2258_ = v___x_2319_;
v___y_2259_ = v___x_2315_;
goto v___jp_2233_;
}
else
{
lean_object* v_val_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2348_; 
v_val_2337_ = lean_ctor_get(v_old_x3f_2097_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_old_x3f_2097_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2339_ = v_old_x3f_2097_;
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_val_2337_);
lean_dec(v_old_x3f_2097_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_elabSnap_2341_; lean_object* v_stx_2342_; lean_object* v_elabSnap_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v_elabSnap_2341_ = lean_ctor_get(v_val_2337_, 3);
lean_inc_ref(v_elabSnap_2341_);
v_stx_2342_ = lean_ctor_get(v_val_2337_, 1);
lean_inc(v_stx_2342_);
lean_dec(v_val_2337_);
v_elabSnap_2343_ = lean_ctor_get(v_elabSnap_2341_, 1);
lean_inc_ref(v_elabSnap_2343_);
lean_dec_ref(v_elabSnap_2341_);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_stx_2342_);
lean_ctor_set(v___x_2344_, 1, v_elabSnap_2343_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2344_);
v___x_2346_ = v___x_2339_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_inc_ref(v___x_2314_);
lean_inc_ref(v___x_2322_);
v___y_2234_ = v___x_2305_;
v___y_2235_ = v___x_2319_;
v___y_2236_ = v___x_2315_;
v___y_2237_ = v___x_2322_;
v___y_2238_ = v___x_2315_;
v___y_2239_ = v___x_2314_;
v___y_2240_ = v___x_2318_;
v___y_2241_ = v___x_2316_;
v___y_2242_ = v___x_2328_;
v___y_2243_ = v___x_2318_;
v___y_2244_ = v___x_2322_;
v___y_2245_ = v___x_2315_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2305_;
v___y_2248_ = v___x_2326_;
v___y_2249_ = v___x_2330_;
v___y_2250_ = v___x_2314_;
v___y_2251_ = v___y_2292_;
v___y_2252_ = v___x_2315_;
v___y_2253_ = v___x_2297_;
v___y_2254_ = v___y_2293_;
v___y_2255_ = v___x_2316_;
v___y_2256_ = v___x_2324_;
v___y_2257_ = v___x_2315_;
v___y_2258_ = v___x_2319_;
v___y_2259_ = v___x_2346_;
goto v___jp_2233_;
}
}
}
}
v___jp_2349_:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2352_);
lean_inc(v_fst_2094_);
v___x_2354_ = l_Lean_Parser_isTerminalCommand(v_fst_2094_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v_toProcessingContext_2356_; lean_object* v_pos_2357_; lean_object* v_endPos_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2355_ = lean_io_promise_new();
v_toProcessingContext_2356_ = lean_ctor_get(v_a_2084_, 0);
v_pos_2357_ = lean_ctor_get(v_fst_2082_, 0);
v_endPos_2358_ = lean_ctor_get(v_toProcessingContext_2356_, 3);
lean_inc(v___x_2355_);
v___x_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2355_);
v___x_2360_ = lean_box(0);
lean_inc(v_endPos_2358_);
lean_inc(v_pos_2357_);
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_pos_2357_);
lean_ctor_set(v___x_2361_, 1, v_endPos_2358_);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_parseCancelTk_2098_);
v___x_2364_ = l_IO_Promise_result_x21___redArg(v___x_2355_);
lean_dec(v___x_2355_);
v___x_2365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2360_);
lean_ctor_set(v___x_2365_, 1, v___x_2362_);
lean_ctor_set(v___x_2365_, 2, v___x_2363_);
lean_ctor_set(v___x_2365_, 3, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___y_2291_ = v___y_2350_;
v___y_2292_ = v___x_2359_;
v___y_2293_ = v___x_2353_;
v___y_2294_ = v___y_2351_;
v___y_2295_ = v___x_2366_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2367_; 
lean_dec(v_parseCancelTk_2098_);
v___x_2367_ = lean_box(0);
v___y_2291_ = v___y_2350_;
v___y_2292_ = v___x_2367_;
v___y_2293_ = v___x_2353_;
v___y_2294_ = v___y_2351_;
v___y_2295_ = v___x_2367_;
goto v___jp_2290_;
}
}
v___jp_2368_:
{
lean_object* v___x_2371_; 
lean_inc(v_fst_2094_);
v___x_2371_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2094_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_box(0);
v___y_2350_ = v_fst_2369_;
v___y_2351_ = v_snd_2370_;
v___y_2352_ = v___x_2372_;
goto v___jp_2349_;
}
else
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
v_val_2373_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_inc(v_val_2373_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_val_2373_);
lean_ctor_set(v___x_2377_, 1, v_val_2373_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
v___y_2350_ = v_fst_2369_;
v___y_2351_ = v_snd_2370_;
v___y_2352_ = v___x_2379_;
goto v___jp_2349_;
}
}
}
}
v___jp_2382_:
{
if (v___y_2383_ == 0)
{
lean_inc_ref(v_fst_2082_);
lean_inc(v_fst_2094_);
v_fst_2369_ = v_fst_2094_;
v_snd_2370_ = v_fst_2082_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2369_ = v___x_2384_;
v_snd_2370_ = v___x_2385_;
goto v___jp_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2388_ = _args[0];
lean_object* v_val_2389_ = _args[1];
lean_object* v_a_2390_ = _args[2];
lean_object* v_snd_2391_ = _args[3];
lean_object* v___x_2392_ = _args[4];
lean_object* v___x_2393_ = _args[5];
lean_object* v_prom_2394_ = _args[6];
lean_object* v___x_2395_ = _args[7];
lean_object* v___f_2396_ = _args[8];
lean_object* v___f_2397_ = _args[9];
lean_object* v___f_2398_ = _args[10];
lean_object* v_pos_2399_ = _args[11];
lean_object* v_fst_2400_ = _args[12];
lean_object* v_cmdState_2401_ = _args[13];
lean_object* v_opts_2402_ = _args[14];
lean_object* v_old_x3f_2403_ = _args[15];
lean_object* v_parseCancelTk_2404_ = _args[16];
lean_object* v___y_2405_ = _args[17];
_start:
{
uint8_t v_val_45711__boxed_2406_; uint8_t v___x_45714__boxed_2407_; lean_object* v_res_2408_; 
v_val_45711__boxed_2406_ = lean_unbox(v_val_2389_);
v___x_45714__boxed_2407_ = lean_unbox(v___x_2393_);
v_res_2408_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2388_, v_val_45711__boxed_2406_, v_a_2390_, v_snd_2391_, v___x_2392_, v___x_45714__boxed_2407_, v_prom_2394_, v___x_2395_, v___f_2396_, v___f_2397_, v___f_2398_, v_pos_2399_, v_fst_2400_, v_cmdState_2401_, v_opts_2402_, v_old_x3f_2403_, v_parseCancelTk_2404_);
lean_dec_ref(v_opts_2402_);
lean_dec(v_prom_2394_);
lean_dec_ref(v_a_2390_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2411_, lean_object* v_parserState_2412_, lean_object* v_cmdState_2413_, lean_object* v_prom_2414_, uint8_t v_sync_2415_, lean_object* v_parseCancelTk_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_toSnapshot_2420_; lean_object* v_stx_2421_; lean_object* v_parserState_2422_; lean_object* v_elabSnap_2423_; lean_object* v_val_2424_; lean_object* v_newParserState_2425_; lean_object* v___y_2459_; lean_object* v___y_2461_; uint8_t v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; uint8_t v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; uint8_t v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2574_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; 
v___f_2501_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2502_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2503_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2504_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2411_) == 1)
{
lean_object* v_val_2649_; lean_object* v_nextCmdSnap_x3f_2650_; 
v_val_2649_ = lean_ctor_get(v_old_x3f_2411_, 0);
v_nextCmdSnap_x3f_2650_ = lean_ctor_get(v_val_2649_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2650_) == 0)
{
goto v___jp_2616_;
}
else
{
lean_object* v_toSnapshot_2651_; lean_object* v_stx_2652_; lean_object* v_parserState_2653_; lean_object* v_elabSnap_2654_; lean_object* v_val_2655_; lean_object* v___x_2656_; 
v_toSnapshot_2651_ = lean_ctor_get(v_val_2649_, 0);
v_stx_2652_ = lean_ctor_get(v_val_2649_, 1);
v_parserState_2653_ = lean_ctor_get(v_val_2649_, 2);
v_elabSnap_2654_ = lean_ctor_get(v_val_2649_, 3);
v_val_2655_ = lean_ctor_get(v_nextCmdSnap_x3f_2650_, 0);
lean_inc(v_val_2655_);
v___x_2656_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2655_);
if (lean_obj_tag(v___x_2656_) == 1)
{
lean_object* v_val_2657_; lean_object* v_nextCmdSnap_x3f_2658_; 
v_val_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2657_);
lean_dec_ref(v___x_2656_);
v_nextCmdSnap_x3f_2658_ = lean_ctor_get(v_val_2657_, 4);
lean_inc(v_nextCmdSnap_x3f_2658_);
lean_dec(v_val_2657_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2658_) == 0)
{
goto v___jp_2616_;
}
else
{
lean_object* v_val_2659_; lean_object* v___x_2660_; 
v_val_2659_ = lean_ctor_get(v_nextCmdSnap_x3f_2658_, 0);
lean_inc(v_val_2659_);
lean_dec_ref(v_nextCmdSnap_x3f_2658_);
v___x_2660_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2659_);
if (lean_obj_tag(v___x_2660_) == 1)
{
lean_object* v_val_2661_; lean_object* v_parserState_2662_; lean_object* v_pos_2663_; uint8_t v___x_2664_; 
v_val_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_val_2661_);
lean_dec_ref(v___x_2660_);
v_parserState_2662_ = lean_ctor_get(v_val_2661_, 2);
lean_inc_ref(v_parserState_2662_);
lean_dec(v_val_2661_);
v_pos_2663_ = lean_ctor_get(v_parserState_2662_, 0);
lean_inc(v_pos_2663_);
lean_dec_ref(v_parserState_2662_);
v___x_2664_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2663_, v_a_2417_);
lean_dec(v_pos_2663_);
if (v___x_2664_ == 0)
{
goto v___jp_2616_;
}
else
{
lean_inc(v_val_2655_);
lean_inc_ref(v_elabSnap_2654_);
lean_inc_ref(v_parserState_2653_);
lean_inc(v_stx_2652_);
lean_inc_ref(v_toSnapshot_2651_);
lean_dec_ref(v_old_x3f_2411_);
lean_dec(v_parseCancelTk_2416_);
lean_dec_ref(v_cmdState_2413_);
lean_dec_ref(v_parserState_2412_);
lean_inc_ref(v_parserState_2653_);
v_toSnapshot_2420_ = v_toSnapshot_2651_;
v_stx_2421_ = v_stx_2652_;
v_parserState_2422_ = v_parserState_2653_;
v_elabSnap_2423_ = v_elabSnap_2654_;
v_val_2424_ = v_val_2655_;
v_newParserState_2425_ = v_parserState_2653_;
goto v___jp_2419_;
}
}
else
{
lean_dec(v___x_2660_);
goto v___jp_2616_;
}
}
}
else
{
lean_dec(v___x_2656_);
goto v___jp_2616_;
}
}
}
else
{
goto v___jp_2616_;
}
v___jp_2419_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_resultSnap_2428_; lean_object* v_task_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2452_; 
v___x_2426_ = lean_io_promise_new();
v___x_2427_ = l_IO_CancelToken_new();
v_resultSnap_2428_ = lean_ctor_get(v_elabSnap_2423_, 2);
lean_inc_ref(v_resultSnap_2428_);
v_task_2429_ = lean_ctor_get(v_resultSnap_2428_, 3);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_resultSnap_2428_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; lean_object* v_unused_2454_; lean_object* v_unused_2455_; 
v_unused_2453_ = lean_ctor_get(v_resultSnap_2428_, 2);
lean_dec(v_unused_2453_);
v_unused_2454_ = lean_ctor_get(v_resultSnap_2428_, 1);
lean_dec(v_unused_2454_);
v_unused_2455_ = lean_ctor_get(v_resultSnap_2428_, 0);
lean_dec(v_unused_2455_);
v___x_2431_ = v_resultSnap_2428_;
v_isShared_2432_ = v_isSharedCheck_2452_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_task_2429_);
lean_dec(v_resultSnap_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2452_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v_toProcessingContext_2438_; lean_object* v_pos_2439_; lean_object* v_endPos_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2433_ = lean_box(v_sync_2415_);
lean_inc_ref(v_a_2417_);
lean_inc(v___x_2427_);
lean_inc(v___x_2426_);
lean_inc_ref(v_newParserState_2425_);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2434_, 0, v_val_2424_);
lean_closure_set(v___f_2434_, 1, v_newParserState_2425_);
lean_closure_set(v___f_2434_, 2, v___x_2426_);
lean_closure_set(v___f_2434_, 3, v___x_2433_);
lean_closure_set(v___f_2434_, 4, v___x_2427_);
lean_closure_set(v___f_2434_, 5, v_a_2417_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = 1;
v___x_2437_ = l_BaseIO_chainTask___redArg(v_task_2429_, v___f_2434_, v___x_2435_, v___x_2436_);
v_toProcessingContext_2438_ = lean_ctor_get(v_a_2417_, 0);
v_pos_2439_ = lean_ctor_get(v_newParserState_2425_, 0);
lean_inc(v_pos_2439_);
lean_dec_ref(v_newParserState_2425_);
v_endPos_2440_ = lean_ctor_get(v_toProcessingContext_2438_, 3);
v___x_2441_ = lean_box(0);
lean_inc(v_endPos_2440_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_pos_2439_);
lean_ctor_set(v___x_2442_, 1, v_endPos_2440_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2427_);
v___x_2445_ = l_IO_Promise_result_x21___redArg(v___x_2426_);
lean_dec(v___x_2426_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 3, v___x_2445_);
lean_ctor_set(v___x_2431_, 2, v___x_2444_);
lean_ctor_set(v___x_2431_, 1, v___x_2443_);
lean_ctor_set(v___x_2431_, 0, v___x_2441_);
v___x_2447_ = v___x_2431_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2449_, 0, v_toSnapshot_2420_);
lean_ctor_set(v___x_2449_, 1, v_stx_2421_);
lean_ctor_set(v___x_2449_, 2, v_parserState_2422_);
lean_ctor_set(v___x_2449_, 3, v_elabSnap_2423_);
lean_ctor_set(v___x_2449_, 4, v___x_2448_);
v___x_2450_ = lean_io_promise_resolve(v___x_2449_, v_prom_2414_);
lean_dec(v_prom_2414_);
return v___x_2450_;
}
}
}
v___jp_2456_:
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
v___jp_2458_:
{
goto v___jp_2456_;
}
v___jp_2460_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2465_ = l_Lean_Name_str___override(v___y_2461_, v___x_2464_);
v___x_2466_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2467_ = l_Lean_Name_str___override(v___x_2465_, v___x_2466_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2469_ = l_Lean_Name_str___override(v___x_2467_, v___x_2468_);
v___x_2470_ = l_Lean_Name_str___override(v___x_2469_, v___x_2466_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = l_Lean_Name_num___override(v___x_2470_, v___x_2471_);
v___x_2473_ = l_Lean_Name_str___override(v___x_2472_, v___x_2466_);
v___x_2474_ = l_Lean_Name_str___override(v___x_2473_, v___x_2468_);
v___x_2475_ = l_Lean_Name_str___override(v___x_2474_, v___x_2466_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2477_ = l_Lean_Name_str___override(v___x_2475_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2479_ = l_Lean_Name_str___override(v___x_2477_, v___x_2478_);
v___x_2480_ = l_Lean_Name_toString(v___x_2479_, v___y_2462_);
v___x_2481_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2484_ = 0;
v___x_2485_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2485_, 0, v___x_2480_);
lean_ctor_set(v___x_2485_, 1, v___x_2481_);
lean_ctor_set(v___x_2485_, 2, v___x_2482_);
lean_ctor_set(v___x_2485_, 3, v___x_2483_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*4, v___x_2484_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref(v___x_2485_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2485_);
lean_ctor_set(v___x_2488_, 1, v_cmdState_2413_);
v___x_2489_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2482_, v___x_2488_);
lean_inc_ref(v___x_2485_);
v___x_2490_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2482_, v___x_2485_);
v___x_2491_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
lean_inc_ref(v___x_2485_);
v___x_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2485_);
lean_ctor_set(v___x_2492_, 1, v___x_2487_);
lean_ctor_set(v___x_2492_, 2, v___x_2489_);
lean_ctor_set(v___x_2492_, 3, v___x_2490_);
lean_ctor_set(v___x_2492_, 4, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2485_);
lean_ctor_set(v___x_2493_, 1, v___x_2486_);
lean_ctor_set(v___x_2493_, 2, v___y_2463_);
lean_ctor_set(v___x_2493_, 3, v___x_2492_);
lean_ctor_set(v___x_2493_, 4, v___x_2482_);
v___x_2494_ = lean_io_promise_resolve(v___x_2493_, v_prom_2414_);
lean_dec(v_prom_2414_);
v___x_2495_ = lean_box(0);
return v___x_2495_;
}
v___jp_2496_:
{
v___y_2461_ = v___y_2497_;
v___y_2462_ = v___y_2498_;
v___y_2463_ = v___y_2499_;
goto v___jp_2460_;
}
v___jp_2505_:
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2522_);
v___x_2524_ = l_Lean_Parser_isTerminalCommand(v___y_2512_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_io_promise_new();
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
v___x_2527_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2523_, v___y_2506_, v___y_2520_, v___y_2511_, v_a_2417_, v___y_2518_, v___y_2513_, v___y_2516_, v___y_2508_, v___y_2507_, v___y_2514_, v___y_2510_, v___y_2515_, v_prom_2414_, v___x_2504_, v___f_2503_, v___f_2502_, v___f_2501_, v___y_2509_, v___y_2517_, v_cmdState_2413_, v___y_2521_, v___y_2519_, v_old_x3f_2411_, v_parseCancelTk_2416_, v___x_2526_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2521_);
lean_dec(v_prom_2414_);
lean_dec(v___y_2514_);
lean_dec(v___y_2506_);
v___y_2459_ = v___x_2527_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_box(0);
v___x_2529_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2523_, v___y_2506_, v___y_2520_, v___y_2511_, v_a_2417_, v___y_2518_, v___y_2513_, v___y_2516_, v___y_2508_, v___y_2507_, v___y_2514_, v___y_2510_, v___y_2515_, v_prom_2414_, v___x_2504_, v___f_2503_, v___f_2502_, v___f_2501_, v___y_2509_, v___y_2517_, v_cmdState_2413_, v___y_2521_, v___y_2519_, v_old_x3f_2411_, v_parseCancelTk_2416_, v___x_2528_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2521_);
lean_dec(v_prom_2414_);
lean_dec(v___y_2514_);
lean_dec(v___y_2506_);
v___y_2459_ = v___x_2529_;
goto v___jp_2458_;
}
}
v___jp_2530_:
{
lean_object* v___x_2547_; 
lean_inc(v___y_2544_);
v___x_2547_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2544_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
v___y_2506_ = v___y_2531_;
v___y_2507_ = v___y_2532_;
v___y_2508_ = v_fst_2545_;
v___y_2509_ = v___y_2533_;
v___y_2510_ = v___y_2534_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v___y_2544_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v_snd_2546_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v___y_2540_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___x_2548_;
goto v___jp_2505_;
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2557_; 
v_val_2549_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2551_ = v___x_2547_;
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_val_2549_);
lean_dec(v___x_2547_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_inc(v_val_2549_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v_val_2549_);
lean_ctor_set(v___x_2553_, 1, v_val_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2506_ = v___y_2531_;
v___y_2507_ = v___y_2532_;
v___y_2508_ = v_fst_2545_;
v___y_2509_ = v___y_2533_;
v___y_2510_ = v___y_2534_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v___y_2544_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v_snd_2546_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v___y_2540_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___x_2555_;
goto v___jp_2505_;
}
}
}
}
v___jp_2558_:
{
if (v___y_2574_ == 0)
{
lean_inc(v___y_2572_);
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2561_;
v___y_2534_ = v___y_2562_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2567_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2569_;
v___y_2542_ = v___y_2570_;
v___y_2543_ = v___y_2571_;
v___y_2544_ = v___y_2572_;
v_fst_2545_ = v___y_2572_;
v_snd_2546_ = v___y_2573_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v___y_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2561_;
v___y_2534_ = v___y_2562_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2567_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2569_;
v___y_2542_ = v___y_2570_;
v___y_2543_ = v___y_2571_;
v___y_2544_ = v___y_2572_;
v_fst_2545_ = v___x_2575_;
v_snd_2546_ = v___x_2576_;
goto v___jp_2530_;
}
}
v___jp_2577_:
{
uint8_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = l_IO_CancelToken_isSet(v_parseCancelTk_2416_);
v___x_2589_ = 1;
if (v___x_2588_ == 0)
{
lean_dec(v___y_2584_);
if (v_sync_2415_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2590_ = lean_io_promise_new();
v___x_2591_ = lean_io_promise_new();
v___x_2592_ = lean_io_promise_new();
v___x_2593_ = lean_io_promise_new();
v___x_2594_ = l_Lean_internal_cmdlineSnapshots;
v___x_2595_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2587_, v___x_2594_);
lean_dec_ref(v___y_2587_);
if (v___x_2595_ == 0)
{
v___y_2559_ = v___x_2593_;
v___y_2560_ = v___x_2590_;
v___y_2561_ = v___y_2579_;
v___y_2562_ = v___x_2592_;
v___y_2563_ = v___x_2588_;
v___y_2564_ = v___y_2578_;
v___y_2565_ = v___x_2591_;
v___y_2566_ = v___x_2589_;
v___y_2567_ = v___y_2580_;
v___y_2568_ = v___y_2581_;
v___y_2569_ = v___x_2594_;
v___y_2570_ = v___y_2582_;
v___y_2571_ = v___y_2583_;
v___y_2572_ = v___y_2585_;
v___y_2573_ = v___y_2586_;
v___y_2574_ = v___x_2595_;
goto v___jp_2558_;
}
else
{
uint8_t v___x_2596_; 
lean_inc(v___y_2585_);
v___x_2596_ = l_Lean_Parser_isTerminalCommand(v___y_2585_);
if (v___x_2596_ == 0)
{
v___y_2559_ = v___x_2593_;
v___y_2560_ = v___x_2590_;
v___y_2561_ = v___y_2579_;
v___y_2562_ = v___x_2592_;
v___y_2563_ = v___x_2588_;
v___y_2564_ = v___y_2578_;
v___y_2565_ = v___x_2591_;
v___y_2566_ = v___x_2589_;
v___y_2567_ = v___y_2580_;
v___y_2568_ = v___y_2581_;
v___y_2569_ = v___x_2594_;
v___y_2570_ = v___y_2582_;
v___y_2571_ = v___y_2583_;
v___y_2572_ = v___y_2585_;
v___y_2573_ = v___y_2586_;
v___y_2574_ = v___x_2595_;
goto v___jp_2558_;
}
else
{
lean_inc(v___y_2585_);
v___y_2531_ = v___x_2593_;
v___y_2532_ = v___x_2590_;
v___y_2533_ = v___y_2579_;
v___y_2534_ = v___x_2592_;
v___y_2535_ = v___x_2588_;
v___y_2536_ = v___y_2578_;
v___y_2537_ = v___x_2591_;
v___y_2538_ = v___x_2589_;
v___y_2539_ = v___y_2580_;
v___y_2540_ = v___y_2581_;
v___y_2541_ = v___x_2594_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2585_;
v_fst_2545_ = v___y_2585_;
v_snd_2546_ = v___y_2586_;
goto v___jp_2530_;
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
v___x_2597_ = lean_box(v___x_2588_);
v___x_2598_ = lean_box(v___x_2589_);
lean_inc_ref(v_a_2417_);
v___f_2599_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2599_, 0, v___y_2582_);
lean_closure_set(v___f_2599_, 1, v___x_2597_);
lean_closure_set(v___f_2599_, 2, v_a_2417_);
lean_closure_set(v___f_2599_, 3, v___y_2581_);
lean_closure_set(v___f_2599_, 4, v___y_2578_);
lean_closure_set(v___f_2599_, 5, v___x_2598_);
lean_closure_set(v___f_2599_, 6, v_prom_2414_);
lean_closure_set(v___f_2599_, 7, v___x_2504_);
lean_closure_set(v___f_2599_, 8, v___f_2503_);
lean_closure_set(v___f_2599_, 9, v___f_2502_);
lean_closure_set(v___f_2599_, 10, v___f_2501_);
lean_closure_set(v___f_2599_, 11, v___y_2579_);
lean_closure_set(v___f_2599_, 12, v___y_2580_);
lean_closure_set(v___f_2599_, 13, v_cmdState_2413_);
lean_closure_set(v___f_2599_, 14, v___y_2583_);
lean_closure_set(v___f_2599_, 15, v_old_x3f_2411_);
lean_closure_set(v___f_2599_, 16, v_parseCancelTk_2416_);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = lean_io_as_task(v___f_2599_, v___x_2600_);
lean_dec_ref(v___x_2601_);
goto v___jp_2456_;
}
}
else
{
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v_parseCancelTk_2416_);
if (lean_obj_tag(v_old_x3f_2411_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2603_; lean_object* v_children_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_val_2602_ = lean_ctor_get(v_old_x3f_2411_, 0);
lean_inc(v_val_2602_);
lean_dec_ref(v_old_x3f_2411_);
v___x_2603_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2602_);
v_children_2604_ = lean_ctor_get(v___x_2603_, 1);
lean_inc_ref(v_children_2604_);
lean_dec_ref(v___x_2603_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_array_get_size(v_children_2604_);
v___x_2607_ = lean_nat_dec_lt(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v_children_2604_);
v___y_2461_ = v___y_2584_;
v___y_2462_ = v___x_2589_;
v___y_2463_ = v___y_2586_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_nat_dec_le(v___x_2606_, v___x_2606_);
if (v___x_2609_ == 0)
{
if (v___x_2607_ == 0)
{
lean_dec_ref(v_children_2604_);
v___y_2461_ = v___y_2584_;
v___y_2462_ = v___x_2589_;
v___y_2463_ = v___y_2586_;
goto v___jp_2460_;
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = lean_usize_of_nat(v___x_2606_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2604_, v___x_2610_, v___x_2611_, v___x_2608_);
lean_dec_ref(v_children_2604_);
v___y_2497_ = v___y_2584_;
v___y_2498_ = v___x_2589_;
v___y_2499_ = v___y_2586_;
v___y_2500_ = v___x_2612_;
goto v___jp_2496_;
}
}
else
{
size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = ((size_t)0ULL);
v___x_2614_ = lean_usize_of_nat(v___x_2606_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2604_, v___x_2613_, v___x_2614_, v___x_2608_);
lean_dec_ref(v_children_2604_);
v___y_2497_ = v___y_2584_;
v___y_2498_ = v___x_2589_;
v___y_2499_ = v___y_2586_;
v___y_2500_ = v___x_2615_;
goto v___jp_2496_;
}
}
}
else
{
lean_dec(v_old_x3f_2411_);
v___y_2461_ = v___y_2584_;
v___y_2462_ = v___x_2589_;
v___y_2463_ = v___y_2586_;
goto v___jp_2460_;
}
}
}
v___jp_2616_:
{
lean_object* v_env_2617_; lean_object* v_scopes_2618_; lean_object* v___x_2619_; lean_object* v_opts_2620_; lean_object* v_currNamespace_2621_; lean_object* v_openDecls_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_snd_2628_; 
v_env_2617_ = lean_ctor_get(v_cmdState_2413_, 0);
v_scopes_2618_ = lean_ctor_get(v_cmdState_2413_, 2);
v___x_2619_ = l_List_head_x21___redArg(v___x_2504_, v_scopes_2618_);
v_opts_2620_ = lean_ctor_get(v___x_2619_, 1);
lean_inc_ref(v_opts_2620_);
v_currNamespace_2621_ = lean_ctor_get(v___x_2619_, 2);
lean_inc(v_currNamespace_2621_);
v_openDecls_2622_ = lean_ctor_get(v___x_2619_, 3);
lean_inc(v_openDecls_2622_);
lean_dec(v___x_2619_);
lean_inc_ref(v_opts_2620_);
lean_inc_ref(v_env_2617_);
v___x_2623_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2623_, 0, v_env_2617_);
lean_ctor_set(v___x_2623_, 1, v_opts_2620_);
lean_ctor_set(v___x_2623_, 2, v_currNamespace_2621_);
lean_ctor_set(v___x_2623_, 3, v_openDecls_2622_);
lean_inc_ref(v_parserState_2412_);
lean_inc_ref(v_a_2417_);
v___f_2624_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4), 4, 3);
lean_closure_set(v___f_2624_, 0, v_a_2417_);
lean_closure_set(v___f_2624_, 1, v___x_2623_);
lean_closure_set(v___f_2624_, 2, v_parserState_2412_);
v___x_2625_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_profileit(v___x_2625_, v_opts_2620_, v___f_2624_, v___x_2626_);
v_snd_2628_ = lean_ctor_get(v___x_2627_, 1);
lean_inc(v_snd_2628_);
if (lean_obj_tag(v_old_x3f_2411_) == 1)
{
lean_object* v_val_2629_; lean_object* v_fst_2630_; lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v_pos_2633_; lean_object* v_toSnapshot_2634_; lean_object* v_stx_2635_; lean_object* v_parserState_2636_; lean_object* v_elabSnap_2637_; lean_object* v_nextCmdSnap_x3f_2638_; uint8_t v___x_2639_; 
v_val_2629_ = lean_ctor_get(v_old_x3f_2411_, 0);
v_fst_2630_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_fst_2630_);
lean_dec(v___x_2627_);
v_fst_2631_ = lean_ctor_get(v_snd_2628_, 0);
lean_inc(v_fst_2631_);
v_snd_2632_ = lean_ctor_get(v_snd_2628_, 1);
lean_inc(v_snd_2632_);
lean_dec(v_snd_2628_);
v_pos_2633_ = lean_ctor_get(v_parserState_2412_, 0);
lean_inc(v_pos_2633_);
lean_dec_ref(v_parserState_2412_);
v_toSnapshot_2634_ = lean_ctor_get(v_val_2629_, 0);
v_stx_2635_ = lean_ctor_get(v_val_2629_, 1);
v_parserState_2636_ = lean_ctor_get(v_val_2629_, 2);
v_elabSnap_2637_ = lean_ctor_get(v_val_2629_, 3);
v_nextCmdSnap_x3f_2638_ = lean_ctor_get(v_val_2629_, 4);
lean_inc(v_stx_2635_);
lean_inc(v_fst_2630_);
v___x_2639_ = l_Lean_Syntax_eqWithInfo(v_fst_2630_, v_stx_2635_);
if (v___x_2639_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2638_) == 0)
{
lean_inc_ref(v_opts_2620_);
lean_inc(v_fst_2631_);
lean_inc(v_fst_2630_);
v___y_2578_ = v___x_2626_;
v___y_2579_ = v_pos_2633_;
v___y_2580_ = v_fst_2630_;
v___y_2581_ = v_snd_2632_;
v___y_2582_ = v_fst_2631_;
v___y_2583_ = v_opts_2620_;
v___y_2584_ = v___x_2626_;
v___y_2585_ = v_fst_2630_;
v___y_2586_ = v_fst_2631_;
v___y_2587_ = v_opts_2620_;
goto v___jp_2577_;
}
else
{
lean_object* v_val_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_val_2640_ = lean_ctor_get(v_nextCmdSnap_x3f_2638_, 0);
v___x_2641_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2640_);
v___x_2642_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2641_, v_val_2640_);
lean_inc_ref(v_opts_2620_);
lean_inc(v_fst_2631_);
lean_inc(v_fst_2630_);
v___y_2578_ = v___x_2626_;
v___y_2579_ = v_pos_2633_;
v___y_2580_ = v_fst_2630_;
v___y_2581_ = v_snd_2632_;
v___y_2582_ = v_fst_2631_;
v___y_2583_ = v_opts_2620_;
v___y_2584_ = v___x_2626_;
v___y_2585_ = v_fst_2630_;
v___y_2586_ = v_fst_2631_;
v___y_2587_ = v_opts_2620_;
goto v___jp_2577_;
}
}
else
{
lean_inc(v_val_2629_);
lean_dec(v_pos_2633_);
lean_dec(v_snd_2632_);
lean_dec(v_fst_2630_);
lean_dec_ref(v_old_x3f_2411_);
lean_dec_ref(v_opts_2620_);
lean_dec(v_parseCancelTk_2416_);
lean_dec_ref(v_cmdState_2413_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2638_) == 1)
{
lean_object* v_val_2643_; 
lean_inc_ref(v_nextCmdSnap_x3f_2638_);
lean_inc_ref(v_elabSnap_2637_);
lean_inc_ref(v_parserState_2636_);
lean_inc(v_stx_2635_);
lean_inc_ref(v_toSnapshot_2634_);
lean_dec(v_val_2629_);
v_val_2643_ = lean_ctor_get(v_nextCmdSnap_x3f_2638_, 0);
lean_inc(v_val_2643_);
lean_dec_ref(v_nextCmdSnap_x3f_2638_);
v_toSnapshot_2420_ = v_toSnapshot_2634_;
v_stx_2421_ = v_stx_2635_;
v_parserState_2422_ = v_parserState_2636_;
v_elabSnap_2423_ = v_elabSnap_2637_;
v_val_2424_ = v_val_2643_;
v_newParserState_2425_ = v_fst_2631_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2644_; 
lean_dec(v_fst_2631_);
v___x_2644_ = lean_io_promise_resolve(v_val_2629_, v_prom_2414_);
lean_dec(v_prom_2414_);
return v___x_2644_;
}
}
}
else
{
lean_object* v_fst_2645_; lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v_pos_2648_; 
v_fst_2645_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_fst_2645_);
lean_dec(v___x_2627_);
v_fst_2646_ = lean_ctor_get(v_snd_2628_, 0);
lean_inc(v_fst_2646_);
v_snd_2647_ = lean_ctor_get(v_snd_2628_, 1);
lean_inc(v_snd_2647_);
lean_dec(v_snd_2628_);
v_pos_2648_ = lean_ctor_get(v_parserState_2412_, 0);
lean_inc(v_pos_2648_);
lean_dec_ref(v_parserState_2412_);
lean_inc_ref(v_opts_2620_);
lean_inc(v_fst_2646_);
lean_inc(v_fst_2645_);
v___y_2578_ = v___x_2626_;
v___y_2579_ = v_pos_2648_;
v___y_2580_ = v_fst_2645_;
v___y_2581_ = v_snd_2647_;
v___y_2582_ = v_fst_2646_;
v___y_2583_ = v_opts_2620_;
v___y_2584_ = v___x_2626_;
v___y_2585_ = v_fst_2645_;
v___y_2586_ = v_fst_2646_;
v___y_2587_ = v_opts_2620_;
goto v___jp_2577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2665_, lean_object* v_newParserState_2666_, lean_object* v_val_2667_, uint8_t v_sync_2668_, lean_object* v_val_2669_, lean_object* v_a_2670_, lean_object* v_oldNext_2671_){
_start:
{
lean_object* v_cmdState_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_cmdState_2673_ = lean_ctor_get(v_oldResult_2665_, 1);
lean_inc_ref(v_cmdState_2673_);
lean_dec_ref(v_oldResult_2665_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_oldNext_2671_);
v___x_2675_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2674_, v_newParserState_2666_, v_cmdState_2673_, v_val_2667_, v_sync_2668_, v_val_2669_, v_a_2670_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2676_ = _args[0];
lean_object* v_val_2677_ = _args[1];
lean_object* v_fst_2678_ = _args[2];
lean_object* v_val_2679_ = _args[3];
lean_object* v_a_2680_ = _args[4];
lean_object* v_snd_2681_ = _args[5];
lean_object* v___x_2682_ = _args[6];
lean_object* v___x_2683_ = _args[7];
lean_object* v_fst_2684_ = _args[8];
lean_object* v_val_2685_ = _args[9];
lean_object* v_val_2686_ = _args[10];
lean_object* v_val_2687_ = _args[11];
lean_object* v_snd_2688_ = _args[12];
lean_object* v_prom_2689_ = _args[13];
lean_object* v___x_2690_ = _args[14];
lean_object* v___f_2691_ = _args[15];
lean_object* v___f_2692_ = _args[16];
lean_object* v___f_2693_ = _args[17];
lean_object* v_pos_2694_ = _args[18];
lean_object* v_fst_2695_ = _args[19];
lean_object* v_cmdState_2696_ = _args[20];
lean_object* v_opts_2697_ = _args[21];
lean_object* v___x_2698_ = _args[22];
lean_object* v_old_x3f_2699_ = _args[23];
lean_object* v_parseCancelTk_2700_ = _args[24];
lean_object* v_next_x3f_2701_ = _args[25];
lean_object* v___y_2702_ = _args[26];
_start:
{
uint8_t v_val_45496__boxed_2703_; uint8_t v___x_45499__boxed_2704_; lean_object* v_res_2705_; 
v_val_45496__boxed_2703_ = lean_unbox(v_val_2679_);
v___x_45499__boxed_2704_ = lean_unbox(v___x_2683_);
v_res_2705_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2676_, v_val_2677_, v_fst_2678_, v_val_45496__boxed_2703_, v_a_2680_, v_snd_2681_, v___x_2682_, v___x_45499__boxed_2704_, v_fst_2684_, v_val_2685_, v_val_2686_, v_val_2687_, v_snd_2688_, v_prom_2689_, v___x_2690_, v___f_2691_, v___f_2692_, v___f_2693_, v_pos_2694_, v_fst_2695_, v_cmdState_2696_, v_opts_2697_, v___x_2698_, v_old_x3f_2699_, v_parseCancelTk_2700_, v_next_x3f_2701_);
lean_dec_ref(v___x_2698_);
lean_dec_ref(v_opts_2697_);
lean_dec(v_prom_2689_);
lean_dec(v_val_2686_);
lean_dec_ref(v_a_2680_);
lean_dec(v_val_2677_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2706_, lean_object* v_parserState_2707_, lean_object* v_cmdState_2708_, lean_object* v_prom_2709_, lean_object* v_sync_2710_, lean_object* v_parseCancelTk_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
uint8_t v_sync_boxed_2714_; lean_object* v_res_2715_; 
v_sync_boxed_2714_ = lean_unbox(v_sync_2710_);
v_res_2715_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2706_, v_parserState_2707_, v_cmdState_2708_, v_prom_2709_, v_sync_boxed_2714_, v_parseCancelTk_2711_, v_a_2712_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2716_, size_t v_i_2717_, size_t v_stop_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2716_, v_i_2717_, v_stop_2718_, v_b_2719_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2723_, lean_object* v_i_2724_, lean_object* v_stop_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
size_t v_i_boxed_2729_; size_t v_stop_boxed_2730_; lean_object* v_res_2731_; 
v_i_boxed_2729_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_stop_boxed_2730_ = lean_unbox_usize(v_stop_2725_);
lean_dec(v_stop_2725_);
v_res_2731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2723_, v_i_boxed_2729_, v_stop_boxed_2730_, v_b_2726_, v___y_2727_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_as_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2732_, lean_object* v_opt_2733_){
_start:
{
lean_object* v_name_2734_; lean_object* v_map_2735_; lean_object* v___x_2736_; 
v_name_2734_ = lean_ctor_get(v_opt_2733_, 0);
v_map_2735_ = lean_ctor_get(v_opts_2732_, 0);
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2735_, v_name_2734_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_box(0);
return v___x_2737_;
}
else
{
lean_object* v_val_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
v_val_2738_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2740_ = v___x_2736_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_val_2738_);
lean_dec(v___x_2736_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
if (lean_obj_tag(v_val_2738_) == 0)
{
lean_object* v_v_2742_; lean_object* v___x_2744_; 
v_v_2742_ = lean_ctor_get(v_val_2738_, 0);
lean_inc_ref(v_v_2742_);
lean_dec_ref(v_val_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_v_2742_);
v___x_2744_ = v___x_2740_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_v_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
else
{
lean_object* v___x_2746_; 
lean_del_object(v___x_2740_);
lean_dec(v_val_2738_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2748_, lean_object* v_opt_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2748_, v_opt_2749_);
lean_dec_ref(v_opt_2749_);
lean_dec_ref(v_opts_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2751_, lean_object* v_x_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2751_);
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2755_, 0, v_x_2752_);
lean_ctor_set(v___x_2755_, 1, v___x_2753_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2762_ = l_Array_toPArray_x27___redArg(v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_List_reverse___redArg(v_a_2764_);
return v___x_2765_;
}
else
{
lean_object* v_head_2766_; lean_object* v_tail_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2780_; 
v_head_2766_ = lean_ctor_get(v_a_2763_, 0);
v_tail_2767_ = lean_ctor_get(v_a_2763_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2769_ = v_a_2763_;
v_isShared_2770_ = v_isSharedCheck_2780_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_tail_2767_);
lean_inc(v_head_2766_);
lean_dec(v_a_2763_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2780_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2771_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_head_2766_);
v___x_2773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
v___x_2774_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v_a_2764_);
lean_ctor_set(v___x_2769_, 0, v___x_2775_);
v___x_2777_ = v___x_2769_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_a_2764_);
v___x_2777_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
v_a_2763_ = v_tail_2767_;
v_a_2764_ = v___x_2777_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2791_; double v___x_2792_; 
v___x_2791_ = lean_unsigned_to_nat(1000000000u);
v___x_2792_ = lean_float_of_nat(v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2800_ = l_Lean_MessageData_ofFormat(v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2801_, lean_object* v_stx_2802_, lean_object* v_toProcessingContext_2803_, lean_object* v___x_2804_, lean_object* v_fileMap_2805_, lean_object* v_parserState_2806_, lean_object* v_a_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_toProcessingContext_2812_; lean_object* v___x_2813_; 
v_toProcessingContext_2812_ = lean_ctor_get(v___y_2810_, 0);
lean_inc_ref(v_toProcessingContext_2812_);
lean_dec_ref(v___y_2810_);
lean_inc(v_stx_2802_);
v___x_2813_ = lean_apply_3(v_setupImports_2801_, v_stx_2802_, v_toProcessingContext_2812_, lean_box(0));
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_3022_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_3022_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_3022_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
if (lean_obj_tag(v_a_2814_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; 
lean_dec_ref(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v_parserState_2806_);
lean_dec_ref(v_fileMap_2805_);
lean_dec(v___x_2804_);
lean_dec_ref(v_toProcessingContext_2803_);
lean_dec(v_stx_2802_);
v_a_2818_ = lean_ctor_get(v_a_2814_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v_a_2814_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v_a_2818_);
v___x_2820_ = v___x_2816_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_3021_; 
v_a_2822_ = lean_ctor_get(v_a_2814_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_a_2814_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2824_ = v_a_2814_;
v_isShared_2825_ = v_isSharedCheck_3021_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v_a_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_3021_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v_mainModuleName_2827_; lean_object* v_package_x3f_2828_; uint8_t v_isModule_2829_; lean_object* v_imports_2830_; lean_object* v_opts_2831_; uint32_t v_trustLevel_2832_; lean_object* v_importArts_2833_; lean_object* v_plugins_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2826_ = lean_io_mono_nanos_now();
v_mainModuleName_2827_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_mainModuleName_2827_);
v_package_x3f_2828_ = lean_ctor_get(v_a_2822_, 1);
lean_inc(v_package_x3f_2828_);
v_isModule_2829_ = lean_ctor_get_uint8(v_a_2822_, sizeof(void*)*6 + 4);
v_imports_2830_ = lean_ctor_get(v_a_2822_, 2);
lean_inc_ref(v_imports_2830_);
v_opts_2831_ = lean_ctor_get(v_a_2822_, 3);
lean_inc_ref(v_opts_2831_);
v_trustLevel_2832_ = lean_ctor_get_uint32(v_a_2822_, sizeof(void*)*6);
v_importArts_2833_ = lean_ctor_get(v_a_2822_, 4);
lean_inc(v_importArts_2833_);
v_plugins_2834_ = lean_ctor_get(v_a_2822_, 5);
lean_inc_ref(v_plugins_2834_);
lean_dec(v_a_2822_);
v___x_2835_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2802_);
v___x_2836_ = l_Lean_MessageLog_empty;
v___x_2837_ = 1;
lean_inc_ref(v_opts_2831_);
v___x_2838_ = l_Lean_Elab_processHeaderCore(v___x_2835_, v_imports_2830_, v_isModule_2829_, v_opts_2831_, v___x_2836_, v_toProcessingContext_2803_, v_trustLevel_2832_, v_plugins_2834_, v___x_2837_, v_mainModuleName_2827_, v_package_x3f_2828_, v_importArts_2833_);
lean_dec(v___x_2835_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_3012_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_3012_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_3012_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_3011_; 
v_fst_2843_ = lean_ctor_get(v_a_2839_, 0);
v_snd_2844_ = lean_ctor_get(v_a_2839_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2846_ = v_a_2839_;
v_isShared_2847_ = v_isSharedCheck_3011_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_snd_2844_);
lean_inc(v_fst_2843_);
lean_dec(v_a_2839_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_3011_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v_traceState_2868_; 
v___x_2848_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2844_);
v___x_2849_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2844_);
v___x_2850_ = l_Lean_MessageLog_hasErrors(v_snd_2844_);
if (v___x_2850_ == 0)
{
double v___x_2961_; double v___x_2962_; double v___x_2963_; double v___x_2964_; double v___x_2965_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_del_object(v___x_2816_);
lean_dec_ref(v___x_2809_);
v___x_2961_ = lean_float_of_nat(v___x_2826_);
v___x_2962_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2963_ = lean_float_div(v___x_2961_, v___x_2962_);
v___x_2964_ = lean_float_of_nat(v___x_2848_);
v___x_2965_ = lean_float_div(v___x_2964_, v___x_2962_);
v___x_2982_ = l_Lean_trace_profiler_output;
v___x_2983_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2831_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
if (v___x_2850_ == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2868_ = v___x_2984_;
goto v___jp_2867_;
}
else
{
goto v___jp_2966_;
}
}
else
{
lean_dec_ref(v___x_2983_);
goto v___jp_2966_;
}
v___jp_2966_:
{
uint64_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2967_ = 0ULL;
v___x_2968_ = lean_box(0);
v___x_2969_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2970_ = lean_box(0);
v___x_2971_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2972_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2972_, 0, v___x_2969_);
lean_ctor_set(v___x_2972_, 1, v___x_2970_);
lean_ctor_set(v___x_2972_, 2, v___x_2971_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3, v___x_2963_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3 + 8, v___x_2965_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*3 + 16, v___x_2837_);
v___x_2973_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2974_ = lean_mk_empty_array_with_capacity(v___x_2804_);
v___x_2975_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2972_);
lean_ctor_set(v___x_2975_, 1, v___x_2973_);
lean_ctor_set(v___x_2975_, 2, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2968_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_mk_empty_array_with_capacity(v___x_2977_);
v___x_2979_ = lean_array_push(v___x_2978_, v___x_2976_);
v___x_2980_ = l_Array_toPArray_x27___redArg(v___x_2979_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set_uint64(v___x_2981_, sizeof(void*)*1, v___x_2967_);
v_traceState_2868_ = v___x_2981_;
goto v___jp_2867_;
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint64_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; size_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
lean_dec(v___x_2848_);
lean_del_object(v___x_2846_);
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_opts_2831_);
lean_dec(v___x_2826_);
lean_del_object(v___x_2824_);
lean_dec(v___x_2808_);
lean_dec_ref(v_parserState_2806_);
lean_dec_ref(v_fileMap_2805_);
lean_dec(v_stx_2802_);
v___x_2985_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2986_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2987_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc(v___x_2804_);
v___x_2988_ = l_Lean_Name_num___override(v___x_2987_, v___x_2804_);
v___x_2989_ = l_Lean_Name_str___override(v___x_2988_, v___x_2985_);
v___x_2990_ = l_Lean_Name_str___override(v___x_2989_, v___x_2986_);
v___x_2991_ = l_Lean_Name_str___override(v___x_2990_, v___x_2985_);
v___x_2992_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2993_ = l_Lean_Name_str___override(v___x_2991_, v___x_2992_);
v___x_2994_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2995_ = l_Lean_Name_str___override(v___x_2993_, v___x_2994_);
v___x_2996_ = l_Lean_Name_toString(v___x_2995_, v___x_2837_);
v___x_2997_ = lean_box(0);
v___x_2998_ = 0ULL;
v___x_2999_ = lean_unsigned_to_nat(32u);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2999_);
v___x_3001_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3002_ = ((size_t)5ULL);
lean_inc(v___x_2804_);
v___x_3003_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3000_);
lean_ctor_set(v___x_3003_, 2, v___x_2804_);
lean_ctor_set(v___x_3003_, 3, v___x_2804_);
lean_ctor_set_usize(v___x_3003_, 4, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set_uint64(v___x_3004_, sizeof(void*)*1, v___x_2998_);
v___x_3005_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3005_, 0, v___x_2996_);
lean_ctor_set(v___x_3005_, 1, v___x_2849_);
lean_ctor_set(v___x_3005_, 2, v___x_2997_);
lean_ctor_set(v___x_3005_, 3, v___x_3004_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*4, v___x_2850_);
v___x_3006_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2809_);
v___x_3007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
lean_ctor_set(v___x_3007_, 2, v___x_2997_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_3007_);
v___x_3009_ = v___x_2816_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
v___jp_2851_:
{
lean_object* v___x_2859_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___y_2857_);
v___x_2859_ = v___x_2824_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___y_2857_);
v___x_2859_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2860_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2860_, 0, v___y_2853_);
lean_ctor_set(v___x_2860_, 1, v___x_2849_);
lean_ctor_set(v___x_2860_, 2, v___x_2859_);
lean_ctor_set(v___x_2860_, 3, v___y_2855_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*4, v___x_2850_);
v___x_2861_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2852_, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2862_, 0, v___y_2854_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
lean_ctor_set(v___x_2862_, 2, v___y_2856_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2862_);
v___x_2864_ = v___x_2841_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
v___jp_2867_:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Language_Lean_reparseOptions(v_opts_2831_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_env_2876_; lean_object* v_messages_2877_; lean_object* v_scopes_2878_; lean_object* v_usedQuotCtxts_2879_; lean_object* v_nextMacroScope_2880_; lean_object* v_maxRecDepth_2881_; lean_object* v_ngen_2882_; lean_object* v_auxDeclNGen_2883_; lean_object* v_snapshotTasks_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2950_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2804_, 3);
v___x_2872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2804_);
lean_ctor_set(v___x_2872_, 1, v___x_2804_);
lean_ctor_set(v___x_2872_, 2, v___x_2804_);
lean_ctor_set(v___x_2872_, 3, v___x_2871_);
lean_ctor_set(v___x_2872_, 4, v___x_2871_);
lean_ctor_set(v___x_2872_, 5, v___x_2871_);
lean_ctor_set(v___x_2872_, 6, v___x_2871_);
lean_ctor_set(v___x_2872_, 7, v___x_2871_);
lean_ctor_set(v___x_2872_, 8, v___x_2871_);
v___x_2873_ = lean_io_promise_new();
v___x_2874_ = l_IO_CancelToken_new();
lean_inc(v_fst_2843_);
v___x_2875_ = l_Lean_Elab_Command_mkState(v_fst_2843_, v_snd_2844_, v_a_2870_);
v_env_2876_ = lean_ctor_get(v___x_2875_, 0);
v_messages_2877_ = lean_ctor_get(v___x_2875_, 1);
v_scopes_2878_ = lean_ctor_get(v___x_2875_, 2);
v_usedQuotCtxts_2879_ = lean_ctor_get(v___x_2875_, 3);
v_nextMacroScope_2880_ = lean_ctor_get(v___x_2875_, 4);
v_maxRecDepth_2881_ = lean_ctor_get(v___x_2875_, 5);
v_ngen_2882_ = lean_ctor_get(v___x_2875_, 6);
v_auxDeclNGen_2883_ = lean_ctor_get(v___x_2875_, 7);
v_snapshotTasks_2884_ = lean_ctor_get(v___x_2875_, 10);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; lean_object* v_unused_2952_; 
v_unused_2951_ = lean_ctor_get(v___x_2875_, 9);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v___x_2875_, 8);
lean_dec(v_unused_2952_);
v___x_2886_ = v___x_2875_;
v_isShared_2887_ = v_isSharedCheck_2950_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_snapshotTasks_2884_);
lean_inc(v_auxDeclNGen_2883_);
lean_inc(v_ngen_2882_);
lean_inc(v_maxRecDepth_2881_);
lean_inc(v_nextMacroScope_2880_);
lean_inc(v_usedQuotCtxts_2879_);
lean_inc(v_scopes_2878_);
lean_inc(v_messages_2877_);
lean_inc(v_env_2876_);
lean_dec(v___x_2875_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2950_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2888_ = lean_box(0);
v___x_2889_ = l_Lean_Options_empty;
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2894_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2894_, 0, v_fst_2843_);
lean_ctor_set(v___x_2894_, 1, v___x_2888_);
lean_ctor_set(v___x_2894_, 2, v_fileMap_2805_);
lean_ctor_set(v___x_2894_, 3, v___x_2872_);
lean_ctor_set(v___x_2894_, 4, v___x_2889_);
lean_ctor_set(v___x_2894_, 5, v___x_2890_);
lean_ctor_set(v___x_2894_, 6, v___x_2891_);
lean_ctor_set(v___x_2894_, 7, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2802_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v_stx_2802_);
lean_ctor_set(v___x_2846_, 0, v___x_2896_);
v___x_2898_ = v___x_2846_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_stx_2802_);
v___x_2898_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = lean_unsigned_to_nat(2u);
v___x_2901_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2900_);
v___x_2902_ = l_Lean_Syntax_getArgs(v___x_2901_);
lean_dec(v___x_2901_);
v___x_2903_ = lean_array_to_list(v___x_2902_);
v___x_2904_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2903_, v___x_2891_);
v___x_2905_ = l_List_toPArray_x27___redArg(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2899_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2895_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_2909_ = lean_array_push(v___x_2908_, v___x_2907_);
v___x_2910_ = l_Array_toPArray_x27___redArg(v___x_2909_);
lean_dec_ref(v___x_2909_);
lean_inc_ref(v___x_2910_);
v___x_2911_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2911_, 0, v___x_2871_);
lean_ctor_set(v___x_2911_, 1, v___x_2871_);
lean_ctor_set(v___x_2911_, 2, v___x_2910_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*3, v___x_2837_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 9, v_traceState_2868_);
lean_ctor_set(v___x_2886_, 8, v___x_2911_);
v___x_2913_ = v___x_2886_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_env_2876_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_messages_2877_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v_scopes_2878_);
lean_ctor_set(v_reuseFailAlloc_2948_, 3, v_usedQuotCtxts_2879_);
lean_ctor_set(v_reuseFailAlloc_2948_, 4, v_nextMacroScope_2880_);
lean_ctor_set(v_reuseFailAlloc_2948_, 5, v_maxRecDepth_2881_);
lean_ctor_set(v_reuseFailAlloc_2948_, 6, v_ngen_2882_);
lean_ctor_set(v_reuseFailAlloc_2948_, 7, v_auxDeclNGen_2883_);
lean_ctor_set(v_reuseFailAlloc_2948_, 8, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2948_, 9, v_traceState_2868_);
lean_ctor_set(v_reuseFailAlloc_2948_, 10, v_snapshotTasks_2884_);
v___x_2913_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; lean_object* v_size_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint64_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
lean_inc(v___x_2874_);
lean_inc(v___x_2873_);
lean_inc_ref(v___x_2913_);
v___x_2914_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2888_, v_parserState_2806_, v___x_2913_, v___x_2873_, v___x_2837_, v___x_2874_, v_a_2807_);
v___x_2915_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2916_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2917_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc(v___x_2804_);
v___x_2918_ = l_Lean_Name_num___override(v___x_2917_, v___x_2804_);
v___x_2919_ = lean_unsigned_to_nat(32u);
v___x_2920_ = lean_mk_empty_array_with_capacity(v___x_2919_);
v___x_2921_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2922_ = ((size_t)5ULL);
lean_inc_n(v___x_2804_, 2);
v___x_2923_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2920_);
lean_ctor_set(v___x_2923_, 2, v___x_2804_);
lean_ctor_set(v___x_2923_, 3, v___x_2804_);
lean_ctor_set_usize(v___x_2923_, 4, v___x_2922_);
v_size_2924_ = lean_ctor_get(v___x_2910_, 2);
lean_inc(v_size_2924_);
v___x_2925_ = l_Lean_Name_str___override(v___x_2918_, v___x_2915_);
v___x_2926_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2808_);
v___x_2927_ = l_Lean_Name_str___override(v___x_2925_, v___x_2916_);
v___x_2928_ = l_Lean_Name_str___override(v___x_2927_, v___x_2915_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2930_ = l_Lean_Name_str___override(v___x_2928_, v___x_2929_);
v___x_2931_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2932_ = l_Lean_Name_str___override(v___x_2930_, v___x_2931_);
v___x_2933_ = l_Lean_Name_toString(v___x_2932_, v___x_2837_);
v___x_2934_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2935_ = 0ULL;
v___x_2936_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2936_, 0, v___x_2923_);
lean_ctor_set_uint64(v___x_2936_, sizeof(void*)*1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2874_);
v___x_2938_ = l_IO_Promise_result_x21___redArg(v___x_2873_);
lean_dec(v___x_2873_);
v___x_2939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2808_);
lean_ctor_set(v___x_2939_, 1, v___x_2926_);
lean_ctor_set(v___x_2939_, 2, v___x_2937_);
lean_ctor_set(v___x_2939_, 3, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2913_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_inc_ref(v___x_2936_);
lean_inc_ref(v___x_2933_);
v___x_2942_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2942_, 0, v___x_2933_);
lean_ctor_set(v___x_2942_, 1, v___x_2934_);
lean_ctor_set(v___x_2942_, 2, v___x_2888_);
lean_ctor_set(v___x_2942_, 3, v___x_2936_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*4, v___x_2850_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_stx_2802_);
v___x_2944_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2945_ = lean_nat_dec_lt(v___x_2804_, v_size_2924_);
lean_dec(v_size_2924_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref(v___x_2910_);
lean_dec(v___x_2804_);
v___x_2946_ = l_outOfBounds___redArg(v___x_2944_);
v___y_2852_ = v___x_2943_;
v___y_2853_ = v___x_2933_;
v___y_2854_ = v___x_2942_;
v___y_2855_ = v___x_2936_;
v___y_2856_ = v___x_2941_;
v___y_2857_ = v___x_2946_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2944_, v___x_2910_, v___x_2804_);
lean_dec(v___x_2804_);
v___y_2852_ = v___x_2943_;
v___y_2853_ = v___x_2933_;
v___y_2854_ = v___x_2942_;
v___y_2855_ = v___x_2936_;
v___y_2856_ = v___x_2941_;
v___y_2857_ = v___x_2947_;
goto v___jp_2851_;
}
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_traceState_2868_);
lean_dec_ref(v___x_2849_);
lean_del_object(v___x_2846_);
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
lean_del_object(v___x_2841_);
lean_del_object(v___x_2824_);
lean_dec(v___x_2808_);
lean_dec_ref(v_parserState_2806_);
lean_dec_ref(v_fileMap_2805_);
lean_dec(v___x_2804_);
lean_dec(v_stx_2802_);
v_a_2953_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2869_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2869_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_opts_2831_);
lean_dec(v___x_2826_);
lean_del_object(v___x_2824_);
lean_del_object(v___x_2816_);
lean_dec_ref(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v_parserState_2806_);
lean_dec_ref(v_fileMap_2805_);
lean_dec(v___x_2804_);
lean_dec(v_stx_2802_);
v_a_3013_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2838_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2838_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v_parserState_2806_);
lean_dec_ref(v_fileMap_2805_);
lean_dec(v___x_2804_);
lean_dec_ref(v_toProcessingContext_2803_);
lean_dec(v_stx_2802_);
v_a_3023_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2813_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2813_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3031_, lean_object* v_stx_3032_, lean_object* v_toProcessingContext_3033_, lean_object* v___x_3034_, lean_object* v_fileMap_3035_, lean_object* v_parserState_3036_, lean_object* v_a_3037_, lean_object* v___x_3038_, lean_object* v___x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3031_, v_stx_3032_, v_toProcessingContext_3033_, v___x_3034_, v_fileMap_3035_, v_parserState_3036_, v_a_3037_, v___x_3038_, v___x_3039_, v___y_3040_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___f_3044_; 
v___x_3043_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3044_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3044_, 0, v___x_3043_);
return v___f_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3045_, lean_object* v_stx_3046_, lean_object* v_parserState_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_toProcessingContext_3050_; lean_object* v_fileMap_3051_; lean_object* v_endPos_3052_; lean_object* v___x_3053_; lean_object* v___f_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_toProcessingContext_3050_ = lean_ctor_get(v_a_3048_, 0);
v_fileMap_3051_ = lean_ctor_get(v_toProcessingContext_3050_, 2);
v_endPos_3052_ = lean_ctor_get(v_toProcessingContext_3050_, 3);
v___x_3053_ = l_Lean_Language_instInhabitedSnapshot_default;
v___f_3054_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3048_);
lean_inc_ref(v_fileMap_3051_);
lean_inc_ref(v_toProcessingContext_3050_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 11, 9);
lean_closure_set(v___f_3057_, 0, v_setupImports_3045_);
lean_closure_set(v___f_3057_, 1, v_stx_3046_);
lean_closure_set(v___f_3057_, 2, v_toProcessingContext_3050_);
lean_closure_set(v___f_3057_, 3, v___x_3056_);
lean_closure_set(v___f_3057_, 4, v_fileMap_3051_);
lean_closure_set(v___f_3057_, 5, v_parserState_3047_);
lean_closure_set(v___f_3057_, 6, v_a_3048_);
lean_closure_set(v___f_3057_, 7, v___x_3055_);
lean_closure_set(v___f_3057_, 8, v___x_3053_);
lean_inc(v_endPos_3052_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v_endPos_3052_);
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
v___x_3060_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3060_, 0, lean_box(0));
lean_closure_set(v___x_3060_, 1, v___f_3054_);
lean_closure_set(v___x_3060_, 2, v___f_3057_);
lean_closure_set(v___x_3060_, 3, v_a_3048_);
v___x_3061_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3055_, v___x_3055_, v___x_3059_, v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3062_, lean_object* v_stx_3063_, lean_object* v_parserState_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3062_, v_stx_3063_, v_parserState_3064_, v_a_3065_);
return v_res_3067_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 1;
v___x_3075_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3076_ = l_Lean_Name_toString(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3077_ = 0;
v___x_3078_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3079_ = lean_box(0);
v___x_3080_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3081_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3082_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
lean_ctor_set(v___x_3082_, 2, v___x_3079_);
lean_ctor_set(v___x_3082_, 3, v___x_3078_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*4, v___x_3077_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3083_, lean_object* v_cmdState_3084_, lean_object* v_a_3085_, lean_object* v_toSnapshot_3086_, lean_object* v_newStx_3087_, lean_object* v_oldCmd_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v_diagnostics_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3117_; 
v___x_3090_ = lean_io_promise_new();
v___x_3091_ = l_IO_CancelToken_new();
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_oldCmd_3088_);
v___x_3093_ = 1;
lean_inc(v___x_3091_);
lean_inc(v___x_3090_);
lean_inc_ref(v_cmdState_3084_);
v___x_3094_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3092_, v_newParserState_3083_, v_cmdState_3084_, v___x_3090_, v___x_3093_, v___x_3091_, v_a_3085_);
v_diagnostics_3095_ = lean_ctor_get(v_toSnapshot_3086_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_toSnapshot_3086_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3118_ = lean_ctor_get(v_toSnapshot_3086_, 3);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_toSnapshot_3086_, 2);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_toSnapshot_3086_, 0);
lean_dec(v_unused_3120_);
v___x_3097_ = v_toSnapshot_3086_;
v_isShared_3098_ = v_isSharedCheck_3117_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_diagnostics_3095_);
lean_dec(v_toSnapshot_3086_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3117_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3099_ = lean_box(0);
v___x_3100_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3101_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3102_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3091_);
v___x_3104_ = l_IO_Promise_result_x21___redArg(v___x_3090_);
lean_dec(v___x_3090_);
v___x_3105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3099_);
lean_ctor_set(v___x_3105_, 1, v___x_3100_);
lean_ctor_set(v___x_3105_, 2, v___x_3103_);
lean_ctor_set(v___x_3105_, 3, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_cmdState_3084_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
v___x_3108_ = 0;
v___x_3109_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v_newStx_3087_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 3, v___x_3102_);
lean_ctor_set(v___x_3097_, 2, v___x_3099_);
lean_ctor_set(v___x_3097_, 0, v___x_3101_);
v___x_3112_ = v___x_3097_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_diagnostics_3095_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v___x_3102_);
v___x_3112_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*4, v___x_3108_);
v___x_3113_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3110_, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3109_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
lean_ctor_set(v___x_3114_, 2, v___x_3107_);
v___x_3115_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3099_, v___x_3114_);
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3121_, lean_object* v_cmdState_3122_, lean_object* v_a_3123_, lean_object* v_toSnapshot_3124_, lean_object* v_newStx_3125_, lean_object* v_oldCmd_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3121_, v_cmdState_3122_, v_a_3123_, v_toSnapshot_3124_, v_newStx_3125_, v_oldCmd_3126_);
lean_dec_ref(v_a_3123_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3129_, lean_object* v_a_3130_, lean_object* v_newStx_3131_, lean_object* v___x_3132_, lean_object* v_oldProcessed_3133_){
_start:
{
lean_object* v_result_x3f_3135_; 
v_result_x3f_3135_ = lean_ctor_get(v_oldProcessed_3133_, 2);
if (lean_obj_tag(v_result_x3f_3135_) == 1)
{
lean_object* v_val_3136_; lean_object* v_firstCmdSnap_3137_; lean_object* v_toSnapshot_3138_; lean_object* v_cmdState_3139_; lean_object* v_stx_x3f_3140_; lean_object* v___f_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; 
v_val_3136_ = lean_ctor_get(v_result_x3f_3135_, 0);
lean_inc(v_val_3136_);
v_firstCmdSnap_3137_ = lean_ctor_get(v_val_3136_, 1);
lean_inc_ref(v_firstCmdSnap_3137_);
v_toSnapshot_3138_ = lean_ctor_get(v_oldProcessed_3133_, 0);
lean_inc_ref(v_toSnapshot_3138_);
lean_dec_ref(v_oldProcessed_3133_);
v_cmdState_3139_ = lean_ctor_get(v_val_3136_, 0);
lean_inc_ref(v_cmdState_3139_);
lean_dec(v_val_3136_);
v_stx_x3f_3140_ = lean_ctor_get(v_firstCmdSnap_3137_, 0);
lean_inc(v_stx_x3f_3140_);
lean_inc_ref(v_a_3130_);
v___f_3141_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3141_, 0, v_newParserState_3129_);
lean_closure_set(v___f_3141_, 1, v_cmdState_3139_);
lean_closure_set(v___f_3141_, 2, v_a_3130_);
lean_closure_set(v___f_3141_, 3, v_toSnapshot_3138_);
lean_closure_set(v___f_3141_, 4, v_newStx_3131_);
v___x_3142_ = lean_box(0);
v___x_3143_ = 1;
v___x_3144_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3137_, v___f_3141_, v_stx_x3f_3140_, v___x_3132_, v___x_3142_, v___x_3143_);
return v___x_3144_;
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v___x_3132_);
lean_dec_ref(v_newParserState_3129_);
v___x_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_newStx_3131_);
v___x_3146_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3145_, v_oldProcessed_3133_);
return v___x_3146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3147_, lean_object* v_a_3148_, lean_object* v_newStx_3149_, lean_object* v___x_3150_, lean_object* v_oldProcessed_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3147_, v_a_3148_, v_newStx_3149_, v___x_3150_, v_oldProcessed_3151_);
lean_dec_ref(v_a_3148_);
return v_res_3153_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3154_ = 0;
v___x_3155_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3156_ = lean_box(0);
v___x_3157_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3158_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3159_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___x_3157_);
lean_ctor_set(v___x_3159_, 2, v___x_3156_);
lean_ctor_set(v___x_3159_, 3, v___x_3155_);
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*4, v___x_3154_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3160_, lean_object* v_a_3161_, lean_object* v_old_3162_, lean_object* v_newStx_3163_, lean_object* v_newParserState_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_result_x3f_3167_; 
v_result_x3f_3167_ = lean_ctor_get(v_old_3162_, 4);
lean_inc(v_result_x3f_3167_);
if (lean_obj_tag(v_result_x3f_3167_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3222_; 
v_val_3168_ = lean_ctor_get(v_result_x3f_3167_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_result_x3f_3167_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3170_ = v_result_x3f_3167_;
v_isShared_3171_ = v_isSharedCheck_3222_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_val_3168_);
lean_dec(v_result_x3f_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3222_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_processedSnap_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3220_; 
v_processedSnap_3172_ = lean_ctor_get(v_val_3168_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_val_3168_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_val_3168_, 0);
lean_dec(v_unused_3221_);
v___x_3174_ = v_val_3168_;
v_isShared_3175_ = v_isSharedCheck_3220_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_processedSnap_3172_);
lean_dec(v_val_3168_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3220_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_toSnapshot_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3215_; 
v_toSnapshot_3176_ = lean_ctor_get(v_old_3162_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_old_3162_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3216_ = lean_ctor_get(v_old_3162_, 4);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_old_3162_, 3);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_old_3162_, 2);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_old_3162_, 1);
lean_dec(v_unused_3219_);
v___x_3178_ = v_old_3162_;
v_isShared_3179_ = v_isSharedCheck_3215_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_toSnapshot_3176_);
lean_dec(v_old_3162_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3215_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_pos_3180_; lean_object* v_endPos_3181_; lean_object* v_stx_x3f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v_diagnostics_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3211_; 
v_pos_3180_ = lean_ctor_get(v_newParserState_3164_, 0);
v_endPos_3181_ = lean_ctor_get(v_toProcessingContext_3160_, 3);
v_stx_x3f_3182_ = lean_ctor_get(v_processedSnap_3172_, 0);
lean_inc(v_stx_x3f_3182_);
lean_inc(v_endPos_3181_);
lean_inc(v_pos_3180_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_pos_3180_);
lean_ctor_set(v___x_3183_, 1, v_endPos_3181_);
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_inc_ref(v___x_3184_);
lean_inc(v_newStx_3163_);
lean_inc_ref(v_a_3161_);
lean_inc_ref(v_newParserState_3164_);
v___f_3185_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3185_, 0, v_newParserState_3164_);
lean_closure_set(v___f_3185_, 1, v_a_3161_);
lean_closure_set(v___f_3185_, 2, v_newStx_3163_);
lean_closure_set(v___f_3185_, 3, v___x_3184_);
v___x_3186_ = lean_box(0);
v___x_3187_ = 1;
v___x_3188_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3172_, v___f_3185_, v_stx_x3f_3182_, v___x_3184_, v___x_3186_, v___x_3187_);
v_diagnostics_3189_ = lean_ctor_get(v_toSnapshot_3176_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_toSnapshot_3176_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; lean_object* v_unused_3213_; lean_object* v_unused_3214_; 
v_unused_3212_ = lean_ctor_get(v_toSnapshot_3176_, 3);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_toSnapshot_3176_, 2);
lean_dec(v_unused_3213_);
v_unused_3214_ = lean_ctor_get(v_toSnapshot_3176_, 0);
lean_dec(v_unused_3214_);
v___x_3191_ = v_toSnapshot_3176_;
v_isShared_3192_ = v_isSharedCheck_3211_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_diagnostics_3189_);
lean_dec(v_toSnapshot_3176_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3211_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3193_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3194_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v___x_3188_);
lean_ctor_set(v___x_3174_, 0, v_newParserState_3164_);
v___x_3196_ = v___x_3174_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_newParserState_3164_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3188_);
v___x_3196_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3196_);
v___x_3198_ = v___x_3170_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3199_ = 0;
v___x_3200_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3163_);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_newStx_3163_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 3, v___x_3194_);
lean_ctor_set(v___x_3191_, 2, v___x_3186_);
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3203_ = v___x_3191_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_diagnostics_3189_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v___x_3194_);
v___x_3203_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*4, v___x_3199_);
v___x_3204_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3201_, v___x_3203_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 4, v___x_3198_);
lean_ctor_set(v___x_3178_, 3, v_newStx_3163_);
lean_ctor_set(v___x_3178_, 2, v_toProcessingContext_3160_);
lean_ctor_set(v___x_3178_, 1, v___x_3204_);
lean_ctor_set(v___x_3178_, 0, v___x_3200_);
v___x_3206_ = v___x_3178_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_toProcessingContext_3160_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_newStx_3163_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___x_3198_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
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
lean_dec(v_result_x3f_3167_);
lean_dec_ref(v_newParserState_3164_);
lean_dec(v_newStx_3163_);
lean_dec_ref(v_toProcessingContext_3160_);
return v_old_3162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3223_, lean_object* v_a_3224_, lean_object* v_old_3225_, lean_object* v_newStx_3226_, lean_object* v_newParserState_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3223_, v_a_3224_, v_old_3225_, v_newStx_3226_, v_newParserState_3227_, v___y_3228_);
lean_dec_ref(v___y_3228_);
lean_dec_ref(v_a_3224_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3231_, lean_object* v_setupImports_3232_, lean_object* v_old_x3f_3233_, lean_object* v___f_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
lean_inc_ref(v_toProcessingContext_3231_);
v___x_3237_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3231_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3307_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3307_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3307_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_snd_3242_; lean_object* v_fst_3243_; lean_object* v_fst_3244_; lean_object* v_snd_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3306_; 
v_snd_3242_ = lean_ctor_get(v_a_3238_, 1);
lean_inc(v_snd_3242_);
v_fst_3243_ = lean_ctor_get(v_a_3238_, 0);
lean_inc(v_fst_3243_);
lean_dec(v_a_3238_);
v_fst_3244_ = lean_ctor_get(v_snd_3242_, 0);
v_snd_3245_ = lean_ctor_get(v_snd_3242_, 1);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_snd_3242_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3247_ = v_snd_3242_;
v_isShared_3248_ = v_isSharedCheck_3306_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_snd_3245_);
lean_inc(v_fst_3244_);
lean_dec(v_snd_3242_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3306_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_MessageLog_hasErrors(v_snd_3245_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___y_3252_; 
lean_inc(v_fst_3243_);
v___x_3250_ = l_Lean_Syntax_unsetTrailing(v_fst_3243_);
if (lean_obj_tag(v_old_x3f_3233_) == 1)
{
lean_object* v_val_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3289_; 
v_val_3273_ = lean_ctor_get(v_old_x3f_3233_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_old_x3f_3233_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3275_ = v_old_x3f_3233_;
v_isShared_3276_ = v_isSharedCheck_3289_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_val_3273_);
lean_dec(v_old_x3f_3233_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3289_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_stx_3277_; lean_object* v_result_x3f_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v_stx_3277_ = lean_ctor_get(v_val_3273_, 3);
v_result_x3f_3278_ = lean_ctor_get(v_val_3273_, 4);
lean_inc(v_stx_3277_);
v___x_3279_ = l_Lean_Syntax_unsetTrailing(v_stx_3277_);
lean_inc(v___x_3250_);
v___x_3280_ = l_Lean_Syntax_eqWithInfo(v___x_3250_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_inc(v_result_x3f_3278_);
lean_del_object(v___x_3275_);
lean_dec(v_val_3273_);
lean_dec_ref(v___f_3234_);
if (lean_obj_tag(v_result_x3f_3278_) == 0)
{
v___y_3252_ = v___y_3235_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3281_; lean_object* v_processedSnap_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_val_3281_ = lean_ctor_get(v_result_x3f_3278_, 0);
lean_inc(v_val_3281_);
lean_dec_ref(v_result_x3f_3278_);
v_processedSnap_3282_ = lean_ctor_get(v_val_3281_, 1);
lean_inc_ref(v_processedSnap_3282_);
lean_dec(v_val_3281_);
v___x_3283_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3284_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3283_, v_processedSnap_3282_);
v___y_3252_ = v___y_3235_;
goto v___jp_3251_;
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3287_; 
lean_dec(v___x_3250_);
lean_del_object(v___x_3247_);
lean_dec(v_snd_3245_);
lean_del_object(v___x_3240_);
lean_dec_ref(v_setupImports_3232_);
lean_dec_ref(v_toProcessingContext_3231_);
lean_inc_ref(v___y_3235_);
v___x_3285_ = lean_apply_5(v___f_3234_, v_val_3273_, v_fst_3243_, v_fst_3244_, v___y_3235_, lean_box(0));
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3285_);
v___x_3287_ = v___x_3275_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_dec_ref(v___f_3234_);
lean_dec(v_old_x3f_3233_);
v___y_3252_ = v___y_3235_;
goto v___jp_3251_;
}
v___jp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3253_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3245_);
lean_inc_ref(v___y_3252_);
lean_inc(v_fst_3244_);
v___x_3254_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3232_, v___x_3250_, v_fst_3244_, v___y_3252_);
v___x_3255_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3256_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_unsigned_to_nat(32u);
v___x_3259_ = lean_mk_empty_array_with_capacity(v___x_3258_);
lean_dec_ref(v___x_3259_);
v___x_3260_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 1, v___x_3254_);
v___x_3262_ = v___x_3247_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_fst_3244_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3254_);
v___x_3262_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3264_, 0, v___x_3255_);
lean_ctor_set(v___x_3264_, 1, v___x_3256_);
lean_ctor_set(v___x_3264_, 2, v___x_3257_);
lean_ctor_set(v___x_3264_, 3, v___x_3260_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*4, v___x_3249_);
lean_inc(v_fst_3243_);
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_fst_3243_);
v___x_3266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3255_);
lean_ctor_set(v___x_3266_, 1, v___x_3253_);
lean_ctor_set(v___x_3266_, 2, v___x_3257_);
lean_ctor_set(v___x_3266_, 3, v___x_3260_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*4, v___x_3249_);
v___x_3267_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3265_, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3264_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
lean_ctor_set(v___x_3268_, 2, v_toProcessingContext_3231_);
lean_ctor_set(v___x_3268_, 3, v_fst_3243_);
lean_ctor_set(v___x_3268_, 4, v___x_3263_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3268_);
v___x_3270_ = v___x_3240_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
lean_del_object(v___x_3247_);
lean_dec(v_fst_3244_);
lean_dec_ref(v___f_3234_);
lean_dec(v_old_x3f_3233_);
lean_dec_ref(v_setupImports_3232_);
v___x_3290_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3245_);
v___x_3291_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3292_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_unsigned_to_nat(32u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
lean_dec_ref(v___x_3295_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3297_, 0, v___x_3291_);
lean_ctor_set(v___x_3297_, 1, v___x_3292_);
lean_ctor_set(v___x_3297_, 2, v___x_3293_);
lean_ctor_set(v___x_3297_, 3, v___x_3296_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*4, v___x_3249_);
lean_inc(v_fst_3243_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_fst_3243_);
v___x_3299_ = 0;
v___x_3300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3300_, 0, v___x_3291_);
lean_ctor_set(v___x_3300_, 1, v___x_3290_);
lean_ctor_set(v___x_3300_, 2, v___x_3293_);
lean_ctor_set(v___x_3300_, 3, v___x_3296_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*4, v___x_3299_);
v___x_3301_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3298_, v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
lean_ctor_set(v___x_3302_, 2, v_toProcessingContext_3231_);
lean_ctor_set(v___x_3302_, 3, v_fst_3243_);
lean_ctor_set(v___x_3302_, 4, v___x_3293_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3302_);
v___x_3304_ = v___x_3240_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v___f_3234_);
lean_dec(v_old_x3f_3233_);
lean_dec_ref(v_setupImports_3232_);
lean_dec_ref(v_toProcessingContext_3231_);
v_a_3308_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3237_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3237_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3316_, lean_object* v_setupImports_3317_, lean_object* v_old_x3f_3318_, lean_object* v___f_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3316_, v_setupImports_3317_, v_old_x3f_3318_, v___f_3319_, v___y_3320_);
lean_dec_ref(v___y_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3323_, lean_object* v_toProcessingContext_3324_, lean_object* v_x_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3326_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3323_);
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3329_, 0, v_x_3325_);
lean_ctor_set(v___x_3329_, 1, v___x_3326_);
lean_ctor_set(v___x_3329_, 2, v_toProcessingContext_3324_);
lean_ctor_set(v___x_3329_, 3, v___x_3327_);
lean_ctor_set(v___x_3329_, 4, v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3330_, lean_object* v_old_x3f_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_toProcessingContext_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___f_3337_; lean_object* v___f_3338_; 
v_toProcessingContext_3334_ = lean_ctor_get(v_a_3332_, 0);
v___x_3335_ = l_Lean_Language_instInhabitedSnapshot_default;
lean_inc_ref(v_a_3332_);
lean_inc_ref(v_toProcessingContext_3334_);
v___f_3336_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3336_, 0, v_toProcessingContext_3334_);
lean_closure_set(v___f_3336_, 1, v_a_3332_);
lean_inc(v_old_x3f_3331_);
lean_inc_ref(v_toProcessingContext_3334_);
v___f_3337_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3337_, 0, v_toProcessingContext_3334_);
lean_closure_set(v___f_3337_, 1, v_setupImports_3330_);
lean_closure_set(v___f_3337_, 2, v_old_x3f_3331_);
lean_closure_set(v___f_3337_, 3, v___f_3336_);
lean_inc_ref(v_toProcessingContext_3334_);
v___f_3338_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3338_, 0, v___x_3335_);
lean_closure_set(v___f_3338_, 1, v_toProcessingContext_3334_);
if (lean_obj_tag(v_old_x3f_3331_) == 1)
{
lean_object* v_val_3339_; lean_object* v_result_x3f_3340_; 
v_val_3339_ = lean_ctor_get(v_old_x3f_3331_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v_old_x3f_3331_);
v_result_x3f_3340_ = lean_ctor_get(v_val_3339_, 4);
if (lean_obj_tag(v_result_x3f_3340_) == 1)
{
lean_object* v_stx_3341_; lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_stx_3341_ = lean_ctor_get(v_val_3339_, 3);
lean_inc(v_stx_3341_);
v_val_3342_ = lean_ctor_get(v_result_x3f_3340_, 0);
lean_inc(v_val_3339_);
v___x_3343_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3339_);
v___x_3344_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 1)
{
lean_object* v_val_3345_; 
v_val_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref(v___x_3344_);
if (lean_obj_tag(v_val_3345_) == 1)
{
lean_object* v_val_3346_; lean_object* v_firstCmdSnap_3347_; lean_object* v___x_3348_; 
v_val_3346_ = lean_ctor_get(v_val_3345_, 0);
lean_inc(v_val_3346_);
lean_dec_ref(v_val_3345_);
v_firstCmdSnap_3347_ = lean_ctor_get(v_val_3346_, 1);
lean_inc_ref(v_firstCmdSnap_3347_);
lean_dec(v_val_3346_);
v___x_3348_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3347_);
if (lean_obj_tag(v___x_3348_) == 1)
{
lean_object* v_val_3349_; lean_object* v_nextCmdSnap_x3f_3350_; 
v_val_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_val_3349_);
lean_dec_ref(v___x_3348_);
v_nextCmdSnap_x3f_3350_ = lean_ctor_get(v_val_3349_, 4);
lean_inc(v_nextCmdSnap_x3f_3350_);
lean_dec(v_val_3349_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3350_) == 0)
{
lean_object* v___x_3351_; 
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3351_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3351_;
}
else
{
lean_object* v_val_3352_; lean_object* v___x_3353_; 
v_val_3352_ = lean_ctor_get(v_nextCmdSnap_x3f_3350_, 0);
lean_inc(v_val_3352_);
lean_dec_ref(v_nextCmdSnap_x3f_3350_);
v___x_3353_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3352_);
if (lean_obj_tag(v___x_3353_) == 1)
{
lean_object* v_val_3354_; lean_object* v_parserState_3355_; lean_object* v_pos_3356_; uint8_t v___x_3357_; 
v_val_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_val_3354_);
lean_dec_ref(v___x_3353_);
v_parserState_3355_ = lean_ctor_get(v_val_3354_, 2);
lean_inc_ref(v_parserState_3355_);
lean_dec(v_val_3354_);
v_pos_3356_ = lean_ctor_get(v_parserState_3355_, 0);
lean_inc(v_pos_3356_);
lean_dec_ref(v_parserState_3355_);
v___x_3357_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3356_, v_a_3332_);
lean_dec(v_pos_3356_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3358_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3358_;
}
else
{
lean_object* v_parserState_3359_; lean_object* v___x_3360_; 
lean_inc_ref(v_toProcessingContext_3334_);
lean_dec_ref(v___f_3338_);
lean_dec_ref(v___f_3337_);
v_parserState_3359_ = lean_ctor_get(v_val_3342_, 0);
lean_inc_ref(v_parserState_3359_);
v___x_3360_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3334_, v_a_3332_, v_val_3339_, v_stx_3341_, v_parserState_3359_, v_a_3332_);
lean_dec_ref(v_a_3332_);
return v___x_3360_;
}
}
else
{
lean_object* v___x_3361_; 
lean_dec(v___x_3353_);
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3361_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3361_;
}
}
}
else
{
lean_object* v___x_3362_; 
lean_dec(v___x_3348_);
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3362_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3362_;
}
}
else
{
lean_object* v___x_3363_; 
lean_dec(v_val_3345_);
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3363_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3363_;
}
}
else
{
lean_object* v___x_3364_; 
lean_dec(v___x_3344_);
lean_dec(v_stx_3341_);
lean_dec(v_val_3339_);
v___x_3364_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3364_;
}
}
else
{
lean_object* v___x_3365_; 
lean_dec(v_val_3339_);
v___x_3365_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3365_;
}
}
else
{
lean_object* v___x_3366_; 
lean_dec(v_old_x3f_3331_);
v___x_3366_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3338_, v___f_3337_, v_a_3332_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3367_, lean_object* v_old_x3f_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3367_, v_old_x3f_3368_, v_a_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3372_, lean_object* v_old_x3f_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
lean_inc(v_old_x3f_3373_);
v___x_3376_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3376_, 0, v_setupImports_3372_);
lean_closure_set(v___x_3376_, 1, v_old_x3f_3373_);
if (lean_obj_tag(v_old_x3f_3373_) == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_box(0);
v___x_3378_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3376_, v___x_3377_, v_a_3374_);
return v___x_3378_;
}
else
{
lean_object* v_val_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3388_; 
v_val_3379_ = lean_ctor_get(v_old_x3f_3373_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_old_x3f_3373_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3381_ = v_old_x3f_3373_;
v_isShared_3382_ = v_isSharedCheck_3388_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_val_3379_);
lean_dec(v_old_x3f_3373_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3388_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_ictx_3383_; lean_object* v___x_3385_; 
v_ictx_3383_ = lean_ctor_get(v_val_3379_, 2);
lean_inc_ref(v_ictx_3383_);
lean_dec(v_val_3379_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v_ictx_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_ictx_3383_);
v___x_3385_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3376_, v___x_3385_, v_a_3374_);
return v___x_3386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3389_, lean_object* v_old_x3f_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_Language_Lean_process(v_setupImports_3389_, v_old_x3f_3390_, v_a_3391_);
lean_dec_ref(v_a_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3394_, lean_object* v_parserState_3395_, lean_object* v_commandState_3396_, lean_object* v_old_x3f_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3407_; 
v___x_3399_ = lean_io_promise_new();
v___x_3400_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3397_) == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_box(0);
v___y_3407_ = v___x_3421_;
goto v___jp_3406_;
}
else
{
lean_object* v_val_3422_; lean_object* v_snd_3423_; lean_object* v___x_3424_; 
v_val_3422_ = lean_ctor_get(v_old_x3f_3397_, 0);
v_snd_3423_ = lean_ctor_get(v_val_3422_, 1);
lean_inc(v_snd_3423_);
v___x_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_snd_3423_);
v___y_3407_ = v___x_3424_;
goto v___jp_3406_;
}
v___jp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3402_, v___y_3403_, v_inputCtx_3394_);
lean_dec(v___x_3404_);
v___x_3405_ = l_IO_Promise_result_x21___redArg(v___x_3399_);
lean_dec(v___x_3399_);
return v___x_3405_;
}
v___jp_3406_:
{
uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = 1;
v___x_3409_ = lean_box(v___x_3408_);
lean_inc(v___x_3399_);
v___x_3410_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3410_, 0, v___y_3407_);
lean_closure_set(v___x_3410_, 1, v_parserState_3395_);
lean_closure_set(v___x_3410_, 2, v_commandState_3396_);
lean_closure_set(v___x_3410_, 3, v___x_3399_);
lean_closure_set(v___x_3410_, 4, v___x_3409_);
lean_closure_set(v___x_3410_, 5, v___x_3400_);
if (lean_obj_tag(v_old_x3f_3397_) == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_box(0);
v___y_3402_ = v___x_3410_;
v___y_3403_ = v___x_3411_;
goto v___jp_3401_;
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_val_3412_ = lean_ctor_get(v_old_x3f_3397_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_old_x3f_3397_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3414_ = v_old_x3f_3397_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v_old_x3f_3397_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_fst_3416_; lean_object* v___x_3418_; 
v_fst_3416_ = lean_ctor_get(v_val_3412_, 0);
lean_inc(v_fst_3416_);
lean_dec(v_val_3412_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v_fst_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_fst_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
v___y_3402_ = v___x_3410_;
v___y_3403_ = v___x_3418_;
goto v___jp_3401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3425_, lean_object* v_parserState_3426_, lean_object* v_commandState_3427_, lean_object* v_old_x3f_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3425_, v_parserState_3426_, v_commandState_3427_, v_old_x3f_3428_);
lean_dec_ref(v_inputCtx_3425_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3431_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3432_; 
v_nextCmdSnap_x3f_3432_ = lean_ctor_get(v_snap_3431_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3434_; 
lean_inc_ref(v_nextCmdSnap_x3f_3432_);
lean_dec_ref(v_snap_3431_);
v_val_3433_ = lean_ctor_get(v_nextCmdSnap_x3f_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref(v_nextCmdSnap_x3f_3432_);
v___x_3434_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3433_);
v_snap_3431_ = v___x_3434_;
goto _start;
}
else
{
lean_object* v_elabSnap_3436_; lean_object* v_resultSnap_3437_; lean_object* v___x_3438_; lean_object* v_cmdState_3439_; lean_object* v___x_3440_; 
v_elabSnap_3436_ = lean_ctor_get(v_snap_3431_, 3);
lean_inc_ref(v_elabSnap_3436_);
lean_dec_ref(v_snap_3431_);
v_resultSnap_3437_ = lean_ctor_get(v_elabSnap_3436_, 2);
lean_inc_ref(v_resultSnap_3437_);
lean_dec_ref(v_elabSnap_3436_);
v___x_3438_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3437_);
v_cmdState_3439_ = lean_ctor_get(v___x_3438_, 1);
lean_inc_ref(v_cmdState_3439_);
lean_dec(v___x_3438_);
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_cmdState_3439_);
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3441_){
_start:
{
lean_object* v_result_x3f_3442_; 
v_result_x3f_3442_ = lean_ctor_get(v_snap_3441_, 4);
lean_inc(v_result_x3f_3442_);
lean_dec_ref(v_snap_3441_);
if (lean_obj_tag(v_result_x3f_3442_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_box(0);
return v___x_3443_;
}
else
{
lean_object* v_val_3444_; lean_object* v_processedSnap_3445_; lean_object* v___x_3446_; lean_object* v_result_x3f_3447_; 
v_val_3444_ = lean_ctor_get(v_result_x3f_3442_, 0);
lean_inc(v_val_3444_);
lean_dec_ref(v_result_x3f_3442_);
v_processedSnap_3445_ = lean_ctor_get(v_val_3444_, 1);
lean_inc_ref(v_processedSnap_3445_);
lean_dec(v_val_3444_);
v___x_3446_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3445_);
v_result_x3f_3447_ = lean_ctor_get(v___x_3446_, 2);
lean_inc(v_result_x3f_3447_);
lean_dec(v___x_3446_);
if (lean_obj_tag(v_result_x3f_3447_) == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_box(0);
return v___x_3448_;
}
else
{
lean_object* v_val_3449_; lean_object* v_firstCmdSnap_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_val_3449_ = lean_ctor_get(v_result_x3f_3447_, 0);
lean_inc(v_val_3449_);
lean_dec_ref(v_result_x3f_3447_);
v_firstCmdSnap_3450_ = lean_ctor_get(v_val_3449_, 1);
lean_inc_ref(v_firstCmdSnap_3450_);
lean_dec(v_val_3449_);
v___x_3451_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3450_);
v___x_3452_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3451_);
return v___x_3452_;
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
